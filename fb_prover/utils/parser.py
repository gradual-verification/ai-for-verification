from typing import List
import re

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