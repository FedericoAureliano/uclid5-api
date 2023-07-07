def indent(s):
    """
    Indent a string
    """
    return "\n".join(["  " + line for line in s.split("\n")])
