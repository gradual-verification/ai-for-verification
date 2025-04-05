import re

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

def extract_components(decls_with_locs, total_line_num):
    components = []

    struct_pattern = re.compile(r'Struct \(loc "(.*?)\((\d+),.*?\)", "(.*?)"', re.DOTALL)
    pred_pattern = re.compile(r'PredFamilyInstanceDecl \(loc "(.*?)\((\d+),.*?\)", "(.*?)"', re.DOTALL)
    func_pattern = re.compile(r'Func \(loc "(.*?)\((\d+),.*?\)".*?, "(.*?)",', re.DOTALL)

    # get the type, name and starting line number of each component
    for decl in decls_with_locs:
        struct_match = struct_pattern.match(decl)
        if struct_match:
            _, line, name = struct_match.groups()
            components.append(('Struct', name, int(line), -1))

        pred_match = pred_pattern.match(decl)
        if pred_match:
            _, line, name = pred_match.groups()
            components.append(('PredFamilyInstanceDecl', name, int(line), -1))

        func_match = func_pattern.match(decl)
        if func_match:
            _, line, name = func_match.groups()
            components.append(('Func', name, int(line), -1))

    # get the ending line number (inclusive) of each component
    new_components = []
    for i, (typ, name, start_line, _) in enumerate(components):
        if i + 1 < len(components):
            end_line = components[i + 1][2] - 1
        else:
            end_line = total_line_num
        new_components.append((typ, name, start_line, end_line))

    return new_components


def extract_predicates(c_text, decls_with_locs, components):
    c_lines = c_text.splitlines()
    pred_occurrences = []
    callexpr_pattern = re.compile(r'CallExpr \(loc "(.*?)\((\d+),(\d+)-(\d+)\)", "(.*?)"', re.DOTALL)

    # get the name and location of all predicates
    pred_names = set()
    for component in components:
        if component[0] == 'PredFamilyInstanceDecl':
            pred_name = component[1]
            pred_names.add(pred_name)

            line = component[2]
            if 0 < line <= len(c_lines):
                line_text = c_lines[line - 1]
                col_start = line_text.find(pred_name)
                if col_start != -1:
                    col_end = col_start + len(pred_name)
                    pred_occurrences.append((pred_name, line, col_start, col_end))

    for decl in decls_with_locs:
        for call_match in callexpr_pattern.finditer(decl):
            _, line, col_start, col_end, called_name = call_match.groups()
            if called_name in pred_names:
                pred_occurrences.append((called_name, int(line), int(col_start), int(col_end) - 1))

    sorted_pred_occurrences = sorted(pred_occurrences, key=lambda x: (x[1], x[2]), reverse=True)
    return sorted_pred_occurrences


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

    #decls = parse_ast(ast_text)

    decls_with_locs = parse_ast(ast_with_locs_text)
    components = extract_components(decls_with_locs, len(c_text.splitlines()))
    preds = extract_predicates(c_text, decls_with_locs, components)
    critical_info = extract_critical_info(c_text, components, preds, "_fbp")
    print("hello")


if __name__ == "__main__":
    main()
