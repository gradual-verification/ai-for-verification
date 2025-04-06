# The occurrence of a predicate
# In the program, it is at the line and in between start_col and end_col (both inclusive)
class PredOccurrence:
    def __init__(self, name: str, line: int, start_col: int, end_col: int):
        self.name = name
        self.line = line
        self.start_col = start_col
        self.end_col = end_col

    def __str__(self):
        return self.name + ', at line ' + str(self.line) + ', col [' + str(self.start_col) + ', ' + str(self.end_col) + ']'