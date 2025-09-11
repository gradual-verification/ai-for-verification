import os
import shutil
from pathlib import Path


# get the list of subdirectory names in the given directory
def get_subdir_names(dir: str, llm: str) -> list:
    subdir_names = []
    with os.scandir(dir) as it:
        for entry in it:
            if entry.is_dir() and entry.name == llm:
                subdir_names.append(entry.name)

    subdir_names.sort()
    return subdir_names


# get the relative path of input files, also sort them at the end
def get_rel_input_files(base_input_folder: str, input_suffixes: tuple[str]) -> list[str]:
    rel_input_files = []

    for dirpath, _, filenames in os.walk(base_input_folder):
        rel_dirpath = os.path.relpath(dirpath, base_input_folder)
        for fname in filenames:
            if fname.endswith(input_suffixes):
                rel_fname = os.path.join(rel_dirpath, fname)
                rel_input_files.append(rel_fname)

    rel_input_files = sorted(rel_input_files)

    return rel_input_files


# given the file path, get the target function to be verified in this file
# based on the pattern that file_name is <benchmark_name>_<target_func_name>_<suffix>
def get_target_func_name(file: str, input_suffixes: tuple[str]) -> str:
    file_name = os.path.basename(file)
    benchmark_name = os.path.basename(os.path.dirname(os.path.dirname(file)))

    for suf in input_suffixes:
        if file_name.endswith(suf):
            # chop off the leading "<benchmark_name>_" and trailing suffix
            return file_name[len(benchmark_name) + 1: - (len(suf) + 1)]

    raise ValueError("filename does not end with a known suffix")


# get the library files inside a directory
def get_lib_files(dir: str) -> list[str]:
    lib_files = []
    with os.scandir(dir) as it:
        for entry in it:
            if entry.is_file() and (entry.name.endswith(".h") or entry.name.endswith(".gh")):
                lib_file = os.path.join(dir, entry.name)
                lib_files.append(lib_file)

    return lib_files


# copy the library files into the new directory
def copy_lib_files(lib_files: list[str], new_dir: str) -> None:
    for lib_file in lib_files:
        lib_file_name = os.path.basename(lib_file)
        new_lib_file = os.path.join(new_dir, lib_file_name)
        copy_content(lib_file, new_lib_file)


# remove the library files in the new directory
def remove_lib_files(lib_files: list[str], new_dir: str) -> None:
    for lib_file in lib_files:
        lib_file_name = os.path.basename(lib_file)
        new_lib_file = os.path.join(new_dir, lib_file_name)
        Path(new_lib_file).unlink(missing_ok=True)


# copy the content from the source file to the destination file
def copy_content(src_file: str, dst_file: str) -> None:
    target = Path(dst_file)
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(src_file, dst_file)