from pathlib import Path
from typing import Tuple, Optional

from function import Function
from clang.cindex import Index, CursorKind, TypeKind, Token


# For a COMPOUND_STMT body, return the tokens/locations of the first '{' and last '}'.
# Falls back to body_cursor.extent if braces not found (should be rare).
def find_body_braces(tu, body_cursor) -> Tuple[Optional[Token], Optional[Token]]:
    btoks = list(tu.get_tokens(extent=body_cursor.extent))
    first_lbrace = next((t for t in btoks if t.spelling == '{'), None)
    last_rbrace  = next((t for t in reversed(btoks) if t.spelling == '}'), None)
    if first_lbrace and last_rbrace:
        return first_lbrace, last_rbrace
    # Fallback
    return None, None


# extract the information of function (declaration/definition/typedef) in the given file.
# The info includes name, line of signature, the range of function body (if any) and its content.
def extract_funcs(filename) -> list[Function]:
    with open(filename) as f:
        all_lines = f.readlines()

    # get the translation unit (AST)
    tu = Index.create().parse(filename, args=["-std=c11"])  # add include paths if needed
    functions = []

    # in the first pass, get the name, line of signature and range of body of functions
    for c in tu.cursor.get_children():
        if c.location.file and c.location.file.name == tu.spelling:
            if c.kind == CursorKind.FUNCTION_DECL:

                name = c.spelling
                sig_start_line = c.extent.start.line
                body_start_line = -1
                body_end_line = -1

                # If it's a definition, locate the body braces precisely
                # the pre&postconditions are extracted by 0-base
                if c.is_definition():
                    for ch in c.get_children():
                        if ch.kind == CursorKind.COMPOUND_STMT:
                            lb_tok, rb_tok = find_body_braces(tu, ch)
                            if lb_tok and rb_tok:
                                body_start_line = lb_tok.location.line
                                body_end_line = rb_tok.location.line
                            break

                func = Function(name, sig_start_line, body_start_line, body_end_line, "")
                functions.append(func)

            elif c.kind == CursorKind.TYPEDEF_DECL:
                t = c.underlying_typedef_type
                if t.kind in (TypeKind.FUNCTIONPROTO, TypeKind.FUNCTIONNOPROTO):
                    name = c.spelling
                    sig_start_line = c.extent.start.line
                    body_start_line = -1
                    body_end_line = -1

                    func = Function(name, sig_start_line, body_start_line, body_end_line, "")
                    functions.append(func)

    # sort by starting line of signature
    functions.sort(key=lambda x: x.sig_start_line)

    # in the second pass, get the content of each function
    for i in range(len(functions)):
        func = functions[i]

        sig_start_line = func.sig_start_line
        body_start_line = func.body_start_line
        body_end_line = func.body_end_line

        # for function definition, get the content till its ending "}"
        if body_start_line >= 0 and body_end_line >= 0:
            content_lines = all_lines[sig_start_line - 1: body_end_line]
        # for function declaration, get the content till the start of next function
        else:
            if i < len(functions) - 1:
                next_func_sig_start_line = functions[i + 1].sig_start_line
                content_lines = all_lines[sig_start_line - 1: next_func_sig_start_line]
            else:
                content_lines = all_lines[sig_start_line - 1:]

        func.content = "".join(content_lines)

    return functions


# extract the struct, predicate or fixpoint definitions before the first function.
# Here, file is the name of the file to be extracted,
# and functions is the list containing the function info
def extract_other_def(file: str, functions: list[Function]) -> str:
    if len(functions) == 0:
        print('No functions found for ' + file)
        return ''

    with open(file) as f:
        all_lines = f.readlines()

    first_func = functions[0]
    return ''.join(all_lines[0 : first_func.sig_start_line - 1])


# in the output file, remove the body of other functions (besides target function)
# so that other functions become a declaration.
def remove_other_func_bodies(target_func_name: str, input_functions: list[Function],
                             output_functions: str, output_file: str, processed_file: str) -> None:
    with open(output_file) as f:
        output_lines = f.readlines()

    for input_func in input_functions:
        if input_func.name != target_func_name:
            for output_func in output_functions:
                if output_func.name == input_func.name:
                    sig_start_line = output_func.sig_start_line
                    body_start_line = output_func.body_start_line
                    body_end_line = output_func.body_end_line

                    # change the source code by lines (0-base)
                    # add ";" at the end of signature
                    if not output_lines[sig_start_line - 1].rstrip().endswith(";"):
                        output_lines[sig_start_line - 1] = output_lines[sig_start_line - 1] + ";"
                    # replace function body with "\n"
                    if body_start_line >= 0 and body_end_line >= 0:
                        for i in range(body_start_line - 1, body_end_line):
                            output_lines[i] = "\n"

    processed_content = ''.join(output_lines)

    target = Path(processed_file)
    target.parent.mkdir(parents=True, exist_ok=True)
    with open(processed_file, "w") as f:
        f.write(processed_content)


# given a function with its content, return its declaration with pre and post.
def get_func_decl(func: Function) -> str:
    content_lines = func.content.splitlines()
    body_start_line = func.body_start_line
    body_end_line = func.body_end_line
    offset = func.sig_start_line - 0

    # change the content by lines (note the offset between content and original source file)
    # add ";" at the end of signature
    if not content_lines[0].rstrip().endswith(";"):
        content_lines[0] = content_lines[0] + ";"
    # replace function body with "\n"
    if body_start_line >= 0 and body_end_line >= 0:
        for i in range(body_start_line, body_end_line + 1):
            content_lines[i - offset] = "\n"

    return "\n".join(content_lines)
