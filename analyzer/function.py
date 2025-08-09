
class Function:
    # if the function doesn't have any body, then its body_start_line and body_end_line are -1.
    def __init__(self, name: str, sig_start_line: int, body_start_line: int,
                 body_end_line: int, content: str):
        self.name = name
        self.sig_start_line = sig_start_line
        self.body_start_line = body_start_line
        self.body_end_line = body_end_line
        self.content = content