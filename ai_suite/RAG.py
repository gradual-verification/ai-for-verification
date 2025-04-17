"""BestRAG"""
import os
# Authors: Abdul Samad Siddiqui <abdulsamadsid1@gmail.com>

import uuid
from typing import List, Optional
from qdrant_client import QdrantClient, models
from qdrant_client.http.models import Distance
from fastembed import TextEmbedding
from fastembed.sparse.bm25 import Bm25



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


    def store_KB_embeddings(self, KB_path: str,
                             metadata: Optional[dict] = None):
        """
        Store the embeddings for each file of knowledge base in the Qdrant collection.

        Args:
            KB_path (str): The path to the knowledge base
            metadata (Optional[dict]): Additional metadata to store with each embedding.
        """

        for filename in os.listdir(KB_path):
            file_path = os.path.join(KB_path, filename)
            if os.path.isfile(file_path):
                with open(file_path, 'r') as file:
                    content = file.read()

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
                    "name": filename
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
                print(f"Stored embedding for file {filename} in collection '{self.collection_name}'.")


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


    def search(self, query: str, rag_type: str, limit: int = 10):
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

        results = self.client.query_points(
            collection_name=self.collection_name,
            query=query_vector[rag_type],
            using=rag_type,
            limit=limit,
        )

        return results


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

