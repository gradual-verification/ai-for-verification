# The basic information of function, where the signature is the string including and after name.
class FunctionInfo:
    def __init__(self, name: str, signature: str, precond: str, postcond: str):
        self.name = name
        self.signature = signature
        self.precond = precond
        self.postcond = postcond

    def __str__(self):
        return self.signature + ', ' + self.precond + ', ' + self.postcond