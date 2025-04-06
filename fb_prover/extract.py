import re
import copy
import subprocess
import sys
from typing import Optional

# The basic information of component (e.g., struct, predicate, function) of a program
# In the program, it is between start_line and end_line (both inclusive)
class ComponentInfo:
    def __init__(self, typ, name, start_line, end_line,
                 name_start_col: Optional[int] = None, name_end_col: Optional[int] = None):
        self.typ = typ
        self.name = name
        self.start_line = start_line
        self.end_line = end_line
        self.name_start_col = name_start_col
        self.name_end_col = name_end_col

    def __str__(self):
        return self.typ + ', ' + self.name + ', at line [' + str(self.start_line) + ', ' + str(self.end_line) + ']'

# The occurrence of a predicate
# In the program, it is at the line and in between start_col and end_col (both inclusive)
class PredOccurrence:
    def __init__(self, name, line, start_col, end_col):
        self.name = name
        self.line = line
        self.start_col = start_col
        self.end_col = end_col

    def __str__(self):
        return self.name + ', at line ' + str(self.line) + ', col [' + str(self.start_col) + ', ' + str(self.end_col) + ']'

# The basic information of function, where the signature is the string including and after name.
class FunctionInfo:
    def __init__(self, name, signature, precond, postcond):
        self.name = name
        self.signature = signature
        self.precond = precond
        self.postcond = postcond

    def __str__(self):
        return self.signature + ', ' + self.precond + ', ' + self.postcond


# Given a text version of ast, this function parses it into a list of strings, with declaration/definitions of components.
def parse_ast(ast):
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
# this function extracts the information of those components and return it.
def extract_component_infos(components_with_locs, total_line_num):
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
def extract_predicate_occurrences(c_text, component_with_locs, component_infos):
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


# Given the program, occurring predicates and a suffix
# this function adds the suffix after all occurring predicates in the program and return a new program
def rename_predicates(c_text, pred_occurrences, suffix):
    c_lines = c_text.splitlines()
    extracted_text = []
    for pred_occurrence in pred_occurrences:
        pred_line = pred_occurrence.line
        line_text = c_lines[pred_line - 1]
        end_loc = pred_occurrence.end_col

        line_text = line_text[:end_loc] + suffix + line_text[end_loc:]
        c_lines[pred_line - 1] = line_text

    return c_lines


# Given a program and the information of components,
# this function extract the definitions of those components (except functions) in the program.
def extract_non_functions(c_text, component_infos):
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
# this function extract the definitions of function (assumed only one).
def extract_function(c_text, component_infos):
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


def main():
    c_file = 'stack_fbp.c'
    #c_file = 'standard_' + orig_c_file
    ast_file = 'ast.txt'
    ast_with_locs_file = 'ast_locs.txt'

    # 1.1 standardize get the ast of the program
    #with open(c_file, 'w') as output_file:
    #    subprocess.run(['clang-format', orig_c_file], stdout = output_file)
    subprocess.run(['verifast', '-dump_ast', ast_file, c_file])
    subprocess.run(['verifast', '-dump_ast_with_locs', ast_with_locs_file, c_file])

    with open(c_file, 'r') as file:
        c_text = file.read()
    with open(ast_file, 'r') as file:
        ast_text = file.read()
    with open(ast_with_locs_file, 'r') as file:
        ast_with_locs_text = file.read()

    # 1.2 get the structure, basic component info and predicate occurrences of original program
    component_with_locs = parse_ast(ast_with_locs_text)
    component_infos = extract_component_infos(component_with_locs, len(c_text.splitlines()))
    pred_occurrences = extract_predicate_occurrences(c_text, component_with_locs, component_infos)

    # 1.3 rename the predicates in the original file
    renamed_c_lines = rename_predicates(c_text, pred_occurrences, '_fbp')
    renamed_c_text = '\n'.join(renamed_c_lines)
    renamed_c_file = 'renamed_' + c_file

    with open(renamed_c_file, 'w') as file:
        file.write(renamed_c_text)

    # 2.1 get the ast of the renamed program
    subprocess.run(['verifast', '-dump_ast', ast_file, renamed_c_file])
    subprocess.run(['verifast', '-dump_ast_with_locs', ast_with_locs_file, renamed_c_file])

    with open(renamed_c_file, 'r') as file:
        renamed_c_text = file.read()
    with open(ast_file, 'r') as file:
        renamed_ast_text = file.read()
    with open(ast_with_locs_file, 'r') as file:
        renamed_ast_with_locs_text = file.read()

    # 2.2 extract the definition of non-functions and functions of the renamed program
    renamed_component_with_locs = parse_ast(renamed_ast_with_locs_text)
    renamed_component_infos = extract_component_infos(renamed_component_with_locs, len(renamed_c_text.splitlines()))

    renamed_non_funcs = extract_non_functions(renamed_c_text, renamed_component_infos)
    renamed_func = extract_function(renamed_c_text, renamed_component_infos)


if __name__ == "__main__":
    main()
