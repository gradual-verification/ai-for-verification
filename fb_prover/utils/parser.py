import copy
import subprocess
import sys
from typing import List, Tuple
import re
from components.component_info import ComponentInfo
from components.function_info import FunctionInfo
from components.pred_occurrence import PredOccurrence


# Given the name of a program
# this function parses such program and return a list of basic component info and a list of occurred predicates
def parse(c_file) -> Tuple[List[ComponentInfo], List[PredOccurrence]]:
    with open(c_file, 'r') as file:
        c_text = file.read()

    # get ast information of the program by using VeriFast
    ast_with_locs_file = 'ast_locs.txt'
    subprocess.run(['verifast', '-dump_ast_with_locs', ast_with_locs_file, c_file])
    with open(ast_with_locs_file, 'r') as file:
        ast_with_locs_text = file.read()

    # get the structure, basic component info and predicate occurrences of the program
    component_with_locs = parse_ast(ast_with_locs_text)
    component_infos = get_component_infos(component_with_locs, len(c_text.splitlines()))
    pred_occurrences = get_predicate_occurrences(c_text, component_with_locs, component_infos)
    return component_infos, pred_occurrences


# Given the name to a program
# this function splits it into the text of non-functions and function.
def split(c_file: str) -> Tuple[List[str], FunctionInfo]:
    # get the program content and basic information of components
    with open(c_file, 'r') as file:
        c_text = file.read()
    component_infos, _ = parse(c_file)

    # extract the text of non-functions and function
    non_funcs = get_non_functions(c_text, component_infos)
    funcs = get_function(c_text, component_infos)
    return non_funcs, funcs


# Given a text version of ast,
# this function parses it into a list of strings, with declaration/definitions of components.
def parse_ast(ast: str) -> List[str]:
    package_decl = re.search(r'PackageDecl \(.*?\[(.*)\]\)', ast, re.DOTALL)
    if not package_decl:
        return []

    pkg_decl = package_decl.group(1)

    decls = []
    i = 0
    n = len(pkg_decl)
    while i < n:
        if pkg_decl[i].isalpha():
            # Start capturing keyword
            keyword_start = i
            while i < n and (pkg_decl[i].isalpha() or pkg_decl[i] == '_'):
                i += 1
            keyword = pkg_decl[keyword_start:i]

            # Skip whitespace between keyword and '('
            while i < n and pkg_decl[i] != '(':
                i += 1
            if i == n:
                break

            # Now capture parentheses content
            paren_count = 0
            content = ''
            while i < n:
                if pkg_decl[i] == '(':
                    paren_count += 1
                elif pkg_decl[i] == ')':
                    paren_count -= 1
                content += pkg_decl[i]
                i += 1
                if paren_count == 0:
                    break

            component = f"{keyword} {content}"
            decls.append(component)
        else:
            i += 1

    return decls


# Given a list of components and the total number of line of the program,
# this function gets the information of those components and return it.
def get_component_infos(components_with_locs: List[str], total_line_num: int) -> List[ComponentInfo]:
    component_infos = []

    struct_pattern = re.compile(r'Struct \(loc "(.*?)\((\d+),.*?\)", "(.*?)"', re.DOTALL)
    pred_pattern = re.compile(r'PredFamilyInstanceDecl \(loc "(.*?)\((\d+),.*?\)", "(.*?)"', re.DOTALL)
    func_pattern = re.compile(r'Func \(loc "(.*?)\((\d+),(\d+)-(\d+)\)".*?, "(.*?)",', re.DOTALL)

    # get the type, name and starting line number of each component
    for component in components_with_locs:
        struct_match = struct_pattern.match(component)
        if struct_match:
            _, line, name = struct_match.groups()
            component_infos.append(ComponentInfo('Struct', name, int(line), -1))

        pred_match = pred_pattern.match(component)
        if pred_match:
            _, line, name = pred_match.groups()
            component_infos.append(ComponentInfo('PredFamilyInstanceDecl', name, int(line), -1))

        func_match = func_pattern.match(component)
        if func_match:
            _, line, start_col, end_col, name = func_match.groups()
            component_infos.append(ComponentInfo('Func', name, int(line), -1, int(start_col), int(end_col)))

    # get the ending line number (inclusive) of each component
    new_component_infos = []
    for i, component_info in enumerate(component_infos):
        if i + 1 < len(component_infos):
            end_line = component_infos[i + 1].start_line - 1
        else:
            end_line = total_line_num

        new_component_info = copy.deepcopy(component_info)
        new_component_info.end_line = end_line
        new_component_infos.append(new_component_info)

    return new_component_infos


# Given the text of program, the components and their basic information,
# this function gets the occurrences of predicates (e.g., definitions and calls)
def get_predicate_occurrences(c_text: str, component_with_locs: List[str],
                              component_infos: List[ComponentInfo]) -> List[PredOccurrence]:
    c_lines = c_text.splitlines()
    pred_occurrences = []
    callexpr_pattern = re.compile(r'CallExpr \(loc "(.*?)\((\d+),(\d+)-(\d+)\)", "(.*?)"', re.DOTALL)

    # get the name and location of predicate declarations
    pred_names = set()
    for component_info in component_infos:
        # todo: double check whether it is true
        if component_info.typ == 'PredFamilyInstanceDecl':
            pred_name = component_info.name
            pred_names.add(pred_name)

            line = component_info.start_line
            if 0 < line <= len(c_lines):
                line_text = c_lines[line - 1]
                start_col = line_text.find(pred_name)
                if start_col != -1:
                    end_col = start_col + len(pred_name)
                    pred_occurrences.append(PredOccurrence(pred_name, line, start_col, end_col))
                else:
                    sys.exit("predicate is not standardized.\n")

    # get the name and location of predicate calls
    for component in component_with_locs:
        for call_match in callexpr_pattern.finditer(component):
            _, line, start_col, end_col, called_name = call_match.groups()
            if called_name in pred_names:
                pred_occurrences.append(PredOccurrence(called_name, int(line), int(start_col), int(end_col) - 1))

    sorted_pred_occurrences = sorted(pred_occurrences, key=lambda x: (x.line, x.start_col), reverse=True)
    return sorted_pred_occurrences


# Given a program and the information of components,
# this function gets the text of those components (except functions) in the program.
def get_non_functions(c_text: str, component_infos: List[ComponentInfo]) -> List[str]:
    c_lines = c_text.splitlines()
    extracted_text = []

    for component_info in component_infos:
        if component_info.typ != 'Func':
            start_line = component_info.start_line
            end_line = component_info.end_line
            # note that the component is at [start_line, end_line] in the file (starting at line 1)
            # so in the list, the component is at [start_line - 1, end_line - 1]
            component_text = c_lines[start_line - 1: end_line]
            extracted_text.append(component_text)

    return extracted_text


# Given a program and the information of components,
# this function gets the definitions of function (assumed only one).
def get_function(c_text: str, component_infos: List[ComponentInfo]) -> FunctionInfo:
    c_lines = c_text.splitlines()

    # get the information of the function
    for component_info in component_infos:
        if component_info.typ == 'Func':
            func_name = component_info.name
            name_start_col = component_info.name_start_col
            start_line = component_info.start_line

            signature = c_lines[start_line - 1][name_start_col - 1:]
            precond = c_lines[start_line]
            postcond = c_lines[start_line + 1]
            return FunctionInfo(func_name, signature, precond, postcond)