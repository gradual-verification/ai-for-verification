from typing import Optional

# The basic information of component (e.g., struct, predicate, function) of a program
# In the program, it is between start_line and end_line (both inclusive)
class ComponentInfo:
    def __init__(self, typ: str, name: str, start_line: int, end_line: int,
                 name_start_col: Optional[int] = None, name_end_col: Optional[int] = None):
        self.typ = typ
        self.name = name
        self.start_line = start_line
        self.end_line = end_line
        self.name_start_col = name_start_col
        self.name_end_col = name_end_col

    def __str__(self):
        return self.typ + ', ' + self.name + ', at line [' + str(self.start_line) + ', ' + str(self.end_line) + ']'