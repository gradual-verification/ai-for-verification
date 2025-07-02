"""BestRAG"""
import os
# Authors: Abdul Samad Siddiqui <abdulsamadsid1@gmail.com>
# from https://github.com/samadpls/BestRAG

import uuid
from typing import List, Optional
from qdrant_client import QdrantClient, models
from qdrant_client.http.models import Distance
from qdrant_client.http import models as rest_models
from fastembed import TextEmbedding
from fastembed.sparse.bm25 import Bm25
import PyPDF2

from configs import tutorial_typename, program_typename


class BestRAG:
    """
    BestRAG (Best Retrieval Augmented by Qdrant) is a class that provides
    functionality for storing and searching document embeddings in a Qdrant
    vector database.

    It supports both dense and sparse embeddings.

    Args:
        url (str): The URL of the Qdrant server.
        api_key (str): The API key for the Qdrant server.
        collection_name (str): The name of the Qdrant collection to use.
    """

    def __init__(self,
                 url: str,
                 api_key: str,
                 collection_name: str,
                 ):
        self.collection_name = collection_name
        self.api_key = api_key
        self.url = url
        self.client = QdrantClient(url=url, api_key=api_key)

        self.dense_model = TextEmbedding()
        self.sparse_model = Bm25("Qdrant/bm25")

        self._create_or_use_collection()


    def _create_or_use_collection(self):
        """
        Create a new Qdrant collection if it doesn't exist, or use an existing one.
        """
        collections = self.client.get_collections()
        collection_names = [
            collection.name for collection in collections.collections]

        if self.collection_name not in collection_names:
            self.client.create_collection(
                collection_name=self.collection_name,
                vectors_config={
                    "dense": models.VectorParams(
                        size=384,
                        distance=Distance.COSINE
                    ),
                },
                sparse_vectors_config={"sparse": models.SparseVectorParams()}
            )

            self.client.create_payload_index(
                collection_name=self.collection_name,
                field_name="type",
                field_schema=rest_models.PayloadSchemaType.KEYWORD,
            )

            print(f"Created collection: {self.collection_name}")
        else:
            print(f"Using existing collection: {self.collection_name}")


    def _get_dense_embedding(self, text: str):
        """
        Get the dense embedding for the given text.

        Args:
            text (str): The text to be embedded.

        Returns:
            List[float]: The dense embedding vector.
        """
        return list(self.dense_model.embed([text]))[0]


    def _get_sparse_embedding(self, text: str):
        """
        Get the sparse embedding for the given text.

        Args:
            text (str): The text to be embedded.

        Returns:
            models.SparseVector: The sparse embedding vector.
        """
        return next(self.sparse_model.embed(text))


    def _extract_pdf_text_per_page(self, pdf_path: str) -> List[str]:
        """
        Load a PDF file and extract the text from each page.

        Args:
            pdf_path (str): The path to the PDF file.

        Returns:
            List[str]: The text from each page of the PDF.
        """
        with open(pdf_path, "rb") as pdf_file:
            reader = PyPDF2.PdfReader(pdf_file)
            return [page.extract_text() for page in reader.pages]


    def store_KB_embeddings(self, KB_path: str,
                           metadata: Optional[dict] = None):
        """
        Store the embeddings for each file of knowledge base into chunks in the Qdrant collection.
        The file may be text or pdf.

        Args:
            KB_path (str): The path to the knowledge base
            metadata (Optional[dict]): Additional metadata to store with each embedding.
        """

        for dirpath, _, file_names in os.walk(KB_path):
            for file_name in file_names:
                file_path = os.path.join(dirpath, file_name)
                if os.path.isfile(file_path):
                    # handle pdf file
                    if "tutorial" in file_path and file_path.endswith(".txt"):
                        with open(file_path, "r") as file:
                            text = file.read()
                            self.store_KB_embedding(file_name, tutorial_typename, text, metadata)
                        #texts = self._extract_pdf_text_per_page(file_path)
                        # store in vector database
                        #for _, text in enumerate(texts):
                        #    self.store_KB_embedding(file_name, tutorial_typename, text, metadata)
                        # store locally
                        #tutorial_text = ""
                        #for _, text in enumerate(texts):
                        #    tutorial_text += text + "\n------------------------------\n"
                        #with open(file_path + ".txt", "w") as text_file:
                        #    text_file.write(tutorial_text)

                    # handle programs
                    elif file_path.endswith(".c") or file_path.endswith(".h") or file_path.endswith(".gh"):
                        with open(file_path, "r") as file:
                            text = file.read()
                        self.store_KB_embedding(file_name, program_typename, text, metadata)


    def store_KB_embedding(self, file_name: str, file_type: str, content: str,
                             metadata: Optional[dict] = None):
        """
        Store the embedding for each chunk of knowledge base in the Qdrant collection.

        Args:
            filename (str): The name of the knowledge base
            content (str): The content of the knowledge base
            metadata (Optional[dict]): Additional metadata to store with each embedding.
        """

        dense_embedding = self._get_dense_embedding(content)
        sparse_embedding = self._get_sparse_embedding(content)

        hybrid_vector = {
            "dense": dense_embedding,
            "sparse": models.SparseVector(
                indices=sparse_embedding.indices,
                values=sparse_embedding.values,
            )
        }

        payload = {
            "text": content,
            "name": file_name,
            "type": file_type,
        }

        if metadata:
            payload.update(metadata)

        point = models.PointStruct(
            id=str(uuid.uuid4()),
            vector=hybrid_vector,
            payload=payload
        )

        self.client.upsert(
            collection_name=self.collection_name,
            points=[point]
        )
        print(f"Stored embedding for file {file_name} in collection '{self.collection_name}'.")


    def delete_KB_embeddings(self, KB_path: str):
        """
        Delete all embeddings associated with a given PDF name from the Qdrant collection.

        Args:
            KB_path (str): The name of the PDF file whose embeddings should be deleted.
        """

        for filename in os.listdir(KB_path):
            file_path = os.path.join(KB_path, filename)
            if os.path.isfile(file_path):
                filter_ = models.Filter(
                    must=[
                        models.FieldCondition(
                            key="name",
                            match=models.MatchValue(value=filename))
                    ]
                )

                result = self.client.delete(
                    collection_name=self.collection_name,
                    points_selector=models.FilterSelector(filter=filter_))

                print(f"Deleted all embeddings for '{filename}' from collection '{self.collection_name}': '{result}'.")


    def search(self, query: str, rag_type: str, file_type: str, limit: int = 10):
        """
        Search the Qdrant collection for documents that match the given query.

        Args:
            query (str): The search query.
            limit (int): The maximum number of results to return. Defaults to 10.

        Returns:
            List[models.SearchResult]: The search results.
        """
        dense_query = self._get_dense_embedding(query)

        sparse_query = self._get_sparse_embedding(query)

        query_vector = {
            "dense": dense_query,
            "sparse": models.SparseVector(
                indices=sparse_query.indices,
                values=sparse_query.values,
            )
        }

        filter = models.Filter(
            must=[
                models.FieldCondition(
                    key="type",
                    match=models.MatchValue(value=file_type)
                )
            ]
        )

        results = self.client.query_points(
            collection_name=self.collection_name,
            query=query_vector[rag_type],
            using=rag_type,
            limit=limit,
            query_filter=filter
        )

        return results


    def delete_collection(self):
        result = self.client.delete_collection(self.collection_name)
        if result:
            print(f"Deleted collection '{self.collection_name}'.")
        else:
            print(f"Failed to delete collection '{self.collection_name}'.")


    def __str__(self):
        """
        Return a string representation of the BestRAG object, including its parameters.
        """
        info = (
            "**************************************************\n"
            "* BestRAG Object Information                     *\n"
            "**************************************************\n"
            f"* URL: {self.url}\n"
            f"* API Key: {self.api_key}\n"
            f"* Collection Name: {self.collection_name}\n"
            "**************************************************"
        )
        return info

