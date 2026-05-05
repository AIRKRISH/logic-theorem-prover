class Formula:
    def __init__(self, type, value=None, left=None, right=None, variable=None):
        self.type = type
        self.value = value
        self.left = left
        self.right = right
        self.variable = variable

    def __repr__(self):
        if self.type == 'ATOM':
            return self.value
        elif self.type == 'NOT':
            return f"~{self.left}"
        elif self.type == 'FORALL':
            return f"(forall {self.variable} {self.left})"
        elif self.type == 'EXISTS':
            return f"(exists {self.variable} {self.left})"
        else:
            return f"({self.left} {self.type} {self.right})"
def parse_atom(s):
    s = s.strip()
    return Formula('ATOM', value=s)
def remove_outer_parentheses(s):
    s = s.strip()
    if s.startswith("(") and s.endswith(")"):
        return s[1:-1].strip()
    return s
def parse_formula(s):
    s = s.strip()
    s = remove_outer_parentheses(s)
    if s.startswith("forall"):
        parts = s.split(" ", 2)
        variable = parts[1]
        inner = parts[2]
        return Formula('FORALL', variable=variable, left=parse_formula(inner))
    if s.startswith("exists"):
        parts = s.split(" ", 2)
        variable = parts[1]
        inner = parts[2]
        return Formula('EXISTS', variable=variable, left=parse_formula(inner))
    if s.startswith("~"):
        inner = s[1:].strip()
        return Formula('NOT', left=parse_formula(inner))
    idx = find_main_operator(s, "->")
    if idx != -1:
        left = s[:idx]
        right = s[idx+2:]
        return Formula('IMPLIES', left=parse_formula(left), right=parse_formula(right))
    idx = find_main_operator(s, "&")
    if idx != -1:
        left = s[:idx]
        right = s[idx+1:]
        return Formula('AND', left=parse_formula(left), right=parse_formula(right))
    idx = find_main_operator(s, "|")
    if idx != -1:
        left = s[:idx]
        right = s[idx+1:]
        return Formula('OR', left=parse_formula(left), right=parse_formula(right))
    return parse_atom(s)
def find_main_operator(s, operator):
    depth = 0
    for i in range(len(s)):
        if s[i] == '(':
            depth += 1
        elif s[i] == ')':
            depth -= 1
        elif depth == 0:
            # check for operator
            if s[i:i+len(operator)] == operator:
                return i
    return -1