import re
import copy

# The basic information of component (e.g., struct, predicate, function) of a program
# In the program, it is between start_line and end_line (both inclusive)
class ComponentInfo:
    def __init__(self, typ, name, start_line, end_line):
        self.typ = typ
        self.name = name
        self.start_line = start_line
        self.end_line = end_line

    def __str__(self):
        return self.typ + ', ' + self.name + ', [' + str(self.start_line) + ', ' + str(self.end_line) + ']'

# The occurrence of a predicate
# In the program, it is at the line and in between start_col and end_col (both inclusive)
class PredOccurrence:
    def __init__(self, name, line, start_col, end_col):
        self.name = name
        self.line = line
        self.start_col = start_col
        self.end_col = end_col

    def __str__(self):
        return self.name + ', ' + str(self.line) + ', [' + str(self.start_col) + ', ' + str(self.end_col) + ']'


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
    func_pattern = re.compile(r'Func \(loc "(.*?)\((\d+),.*?\)".*?, "(.*?)",', re.DOTALL)

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
            _, line, name = func_match.groups()
            component_infos.append(ComponentInfo('Func', name, int(line), -1))

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
def rename_preds(c_text, pred_occurrences, suffix):
    c_lines = c_text.splitlines()
    extracted_text = []
    for pred_occurrence in pred_occurrences:
        pred_line = pred_occurrence.line
        line_text = c_lines[pred_line - 1]
        end_loc = pred_occurrence.end_col

        line_text = line_text[:end_loc] + suffix + line_text[end_loc:]
        c_lines[pred_line - 1] = line_text

    return c_lines


'''
def extract_critical_info(c_text, components, pred_occurrences, suffix):
    c_lines = c_text.splitlines()
    extracted_text = []

    for component in components:
        start_line = component[2]
        end_line = component[3]

        if component[0] == 'PredFamilyInstanceDecl':
            # add suffix for each predicate occurrence (which is traversed reversely)
            for pred_occurrence in pred_occurrences:
                pred_line = pred_occurrence[1]
                # todo: double check bound
                if start_line <= pred_line <= end_line:
                    line_text = c_lines[pred_line - 1]
                    end_loc = pred_occurrence[3]
                    line_text = line_text[:end_loc] + suffix + line_text[end_loc:]
                    c_lines[pred_line - 1] = line_text

            component_text = c_lines[start_line - 1: end_line]
            extracted_text.append(component_text)

        if component[0] == 'Struct':
            component_text = c_lines[start_line - 1: end_line]
            extracted_text.append(component_text)

        if component[0] == 'Func':
            component_text = c_lines[start_line - 1: end_line]
            extracted_text.append(component_text)

    return extracted_text
'''


def main():
    c_file = "stack_fbp.c"
    ast_file = "ast.txt"
    ast_with_locs_file = "ast_locs.txt"

    with open(c_file, 'r') as file:
        c_text = file.read()
    with open(ast_file, 'r') as file:
        ast_text = file.read()
    with open(ast_with_locs_file, 'r') as file:
        ast_with_locs_text = file.read()

    # 1. get the structure, basic component info and predicate occurrences of original program
    component_with_locs = parse_ast(ast_with_locs_text)
    component_infos = extract_component_infos(component_with_locs, len(c_text.splitlines()))
    pred_occurrences = extract_predicate_occurrences(c_text, component_with_locs, component_infos)

    # 2. rename the predicates in the original file
    renamed_c_text = rename_preds(c_text, pred_occurrences, "_fbp")
    #critical_info = extract_critical_info(c_text, components, preds, "_fbp")
    print("hello")


if __name__ == "__main__":
    main()
