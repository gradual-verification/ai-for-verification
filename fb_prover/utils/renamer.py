from utils.extractor import get_basic_info

# Given the name of program, and a suffix
# this function adds the suffix after all predicates occurring in the program,
# write it to a new file and return its name.
def rename_predicates(c_file: str, suffix: str) -> str:
    # get the predicate occurring in this program
    _, pred_occurrences = get_basic_info(c_file)

    with open(c_file, 'r') as file:
        c_text = file.read()
    c_lines = c_text.splitlines()

    # rename each occurrence of predicate
    for pred_occurrence in pred_occurrences:
        pred_line = pred_occurrence.line
        line_text = c_lines[pred_line - 1]
        end_loc = pred_occurrence.end_col

        line_text = line_text[:end_loc] + suffix + line_text[end_loc:]
        c_lines[pred_line - 1] = line_text

    # write the renamed program
    renamed_c_file = 'renamed_' + c_file
    renamed_c_text = '\n'.join(c_lines)
    with open(renamed_c_file, 'w') as file:
        file.write(renamed_c_text)
    return renamed_c_file