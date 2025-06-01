import os
import re


"""
Given a list of filenames of default library, a base folder, 
the path to the c file, and a folder of lib, this function reads the files
being implicitly and explicitly included by the c file and returns them in a mapping.
"""
def read_included_lib_files(filenames: list[str], folder_path: str,
                            c_file_path: str, lib_folder_path: str) -> dict[str, str]:
    with open(c_file_path, 'r', encoding='utf-8') as f:
        input_content = f.read()

    results = {}
    read_implicitly_included_lib_files(filenames, lib_folder_path, results)
    read_explicitly_included_lib_files_recursive(folder_path, input_content, lib_folder_path, results)
    return results


"""
Given the path to a base folder, the path to the c file, and a folder of lib, 
this function extracts the filenames explicitly included by the c file,
and tries to read those files first in the base folder and then in the lib folder.
It will further do the same thing on the included files.

@param folder_path: the folder that user provides, which may store the lib file of user
@param c_file_content: the contents of the c file (might be lib file)
@param lib_folder_path: the folder of lib files
@param results: the mapping from lib file name to content.
"""
def read_explicitly_included_lib_files_recursive(folder_path: str,
                                                c_file_content: str, lib_folder_path: str,
                                                results: dict[str, str]):
    c_lines = c_file_content.splitlines()
    # regex to capture included filenames in the c_file
    # it supports #include, //@ #include, and <lib file>, "lib file"
    include_pattern = re.compile(r'^\s*(?:\/\/@\s*)?#\s*include\s*[<"]([^">]+)[">]')

    included_files = []
    for line in c_lines:
        m = include_pattern.match(line)
        if m:
            filename = m.group(1).strip()
            included_files.append(filename)

    for included_file in included_files:
        # avoid redundant search
        if included_file not in results:
            # first check the lib file in the same directory, then in lib folder
            for base_path in [folder_path, lib_folder_path]:
                lib_file_path = os.path.join(base_path, included_file)
                if os.path.isfile(lib_file_path):
                    with open(lib_file_path, 'r', encoding='utf-8') as lib_file:
                        lib_file_content = lib_file.read()
                    results[included_file] = lib_file_content
                    # recursively searching the files that this lib file includes
                    read_explicitly_included_lib_files_recursive(base_path, lib_file_content, lib_folder_path, results)


"""
Given a list of filenames of default library and a folder of lib, 
this function reads those files in that folder and stores them in a mapping

@param filenames: the list of lib files being included implicitly
@param lib_folder_path: the folder of lib files
@param results: the mapping from lib file name to content.
"""
def read_implicitly_included_lib_files(filenames: list[str], lib_folder_path: str, results: dict[str, str]):
    for filename in filenames:
        if filename not in results:
            lib_file_path = os.path.join(lib_folder_path, filename)
            if os.path.isfile(lib_file_path):
                with open(lib_file_path, 'r', encoding='utf-8') as lib_file:
                    lib_file_content = lib_file.read()
                results[filename] = lib_file_content
