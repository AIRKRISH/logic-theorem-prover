from copy import deepcopy

# ---------------------------------------------------------
# FORMULA
# ---------------------------------------------------------

class Formula:
    def __init__(self, type, left=None, right=None, variable=None, value=None):
        self.type = type
        self.left = left
        self.right = right
        self.variable = variable
        self.value = value

    def __repr__(self):
        if self.type == "ATOM":
            return self.value
        if self.type == "NOT":
            return f"~{self.left}"
        if self.type == "AND":
            return f"({self.left} ∧ {self.right})"
        if self.type == "OR":
            return f"({self.left} ∨ {self.right})"
        if self.type == "IMPLIES":
            return f"({self.left} → {self.right})"
        if self.type == "FORALL":
            return f"∀{self.variable}.{self.left}"
        if self.type == "EXISTS":
            return f"∃{self.variable}.{self.left}"
        return str(self.type)


# ---------------------------------------------------------
# SEQUENT
# ---------------------------------------------------------

class Sequent:
    def __init__(self, left=None, right=None):
        self.left = left if left else []
        self.right = right if right else []

    def __repr__(self):
        return f"{self.left} ⊢ {self.right}"


# ---------------------------------------------------------
# IMPROVED PROVER (Algorithm 2 + Improvements)
# ---------------------------------------------------------

class Prover:
    def __init__(self):
        self.fresh_counter = 0
        self.cache = {}

    # --------------------------
    # AXIOM CHECK
    # --------------------------
    def is_axiom(self, seq):
        for l in seq.left:
            for r in seq.right:
                if str(l) == str(r):
                    return True

        for r in seq.right:
            if r.type == "TOP":
                return True

        for l in seq.left:
            if l.type == "BOTTOM":
                return True

        return False

    # --------------------------
    # FRESH CONSTANT
    # --------------------------
    def fresh(self):
        self.fresh_counter += 1
        return f"c{self.fresh_counter}"

    # --------------------------
    # SUBSTITUTE
    # --------------------------
    def substitute(self, f, var, term):
        if f is None:
            return None

        if f.type == "ATOM":
            return Formula("ATOM", value=f.value.replace(var, term))

        return Formula(
            f.type,
            left=self.substitute(f.left, var, term),
            right=self.substitute(f.right, var, term),
            variable=f.variable,
            value=f.value
        )

    # ---------------------------------------------------------
    # MAIN PROOF SEARCH
    # ---------------------------------------------------------

    def prove(self, seq, depth=0, max_depth=20, visited=None):

        if visited is None:
            visited = set()

        # --------------------------
        # Loop Detection
        # --------------------------
        key = (tuple(map(str, seq.left)), tuple(map(str, seq.right)))

        if key in visited:
            return False

        visited.add(key)

        # --------------------------
        # Memoisation
        # --------------------------
        if key in self.cache:
            return self.cache[key]

        # --------------------------
        # Depth / Quantifier Limit
        # --------------------------
        if depth > max_depth or self.fresh_counter > 20:
            return False

        # --------------------------
        # AXIOM
        # --------------------------
        if self.is_axiom(seq):
            self.cache[key] = True
            return True

        # -------------------------------------------------
        # NON-BRANCHING RULES
        # -------------------------------------------------

        # ¬L
        for i, f in enumerate(seq.left):
            if f.type == "NOT":
                result = self.prove(
                    Sequent(seq.left[:i] + seq.left[i+1:], seq.right + [f.left]),
                    depth + 1, max_depth, visited
                )
                self.cache[key] = result
                return result

        # ¬R
        for i, f in enumerate(seq.right):
            if f.type == "NOT":
                result = self.prove(
                    Sequent(seq.left + [f.left], seq.right[:i] + seq.right[i+1:]),
                    depth + 1, max_depth, visited
                )
                self.cache[key] = result
                return result

        # ∧L
        for i, f in enumerate(seq.left):
            if f.type == "AND":
                result = self.prove(
                    Sequent(seq.left[:i] + seq.left[i+1:] + [f.left, f.right], seq.right),
                    depth + 1, max_depth, visited
                )
                self.cache[key] = result
                return result

        # ∨R
        for i, f in enumerate(seq.right):
            if f.type == "OR":
                result = self.prove(
                    Sequent(seq.left, seq.right[:i] + seq.right[i+1:] + [f.left, f.right]),
                    depth + 1, max_depth, visited
                )
                self.cache[key] = result
                return result

        # →R
        for i, f in enumerate(seq.right):
            if f.type == "IMPLIES":
                result = self.prove(
                    Sequent(seq.left + [f.left],
                            seq.right[:i] + seq.right[i+1:] + [f.right]),
                    depth + 1, max_depth, visited
                )
                self.cache[key] = result
                return result

        # -------------------------------------------------
        # BRANCHING RULES
        # -------------------------------------------------

        # ∧R
        for i, f in enumerate(seq.right):
            if f.type == "AND":
                b1 = Sequent(seq.left, seq.right[:i] + seq.right[i+1:] + [f.left])
                b2 = Sequent(seq.left, seq.right[:i] + seq.right[i+1:] + [f.right])

                result = self.prove(b1, depth + 1, max_depth, visited.copy()) and \
                         self.prove(b2, depth + 1, max_depth, visited.copy())

                self.cache[key] = result
                return result

        # ∨L
        for i, f in enumerate(seq.left):
            if f.type == "OR":
                b1 = Sequent(seq.left[:i] + seq.left[i+1:] + [f.left], seq.right)
                b2 = Sequent(seq.left[:i] + seq.left[i+1:] + [f.right], seq.right)

                result = self.prove(b1, depth + 1, max_depth, visited.copy()) and \
                         self.prove(b2, depth + 1, max_depth, visited.copy())

                self.cache[key] = result
                return result

        # →L
        for i, f in enumerate(seq.left):
            if f.type == "IMPLIES":
                b1 = Sequent(seq.left[:i] + seq.left[i+1:], seq.right + [f.left])
                b2 = Sequent(seq.left[:i] + seq.left[i+1:] + [f.right], seq.right)

                result = self.prove(b1, depth + 1, max_depth, visited.copy()) and \
                         self.prove(b2, depth + 1, max_depth, visited.copy())

                self.cache[key] = result
                return result

        # -------------------------------------------------
        # QUANTIFIERS (naive but controlled)
        # -------------------------------------------------

        # ∀R
        for i, f in enumerate(seq.right):
            if f.type == "FORALL":
                t = self.fresh()
                inst = self.substitute(f.left, f.variable, t)

                result = self.prove(
                    Sequent(seq.left, seq.right[:i] + seq.right[i+1:] + [inst]),
                    depth + 1, max_depth, visited
                )
                self.cache[key] = result
                return result

        # ∃L
        for i, f in enumerate(seq.left):
            if f.type == "EXISTS":
                t = self.fresh()
                inst = self.substitute(f.left, f.variable, t)

                result = self.prove(
                    Sequent(seq.left[:i] + seq.left[i+1:] + [inst], seq.right),
                    depth + 1, max_depth, visited
                )
                self.cache[key] = result
                return result
        # ∀L
        for i, f in enumerate(seq.left):
            if f.type == "FORALL":
                t = self.fresh()
                inst = self.substitute(f.left, f.variable, t)

                result = self.prove(
                    Sequent(seq.left + [inst], seq.right),
                    depth + 1, max_depth, visited
                )
                self.cache[key] = result
                return result

        # ∃R
        for i, f in enumerate(seq.right):
            if f.type == "EXISTS":
                t = self.fresh()
                inst = self.substitute(f.left, f.variable, t)

                result = self.prove(
                    Sequent(seq.left, seq.right + [inst]),
                    depth + 1, max_depth, visited
                )
                self.cache[key] = result
                return result

        # -------------------------------------------------
        # FAIL
        # -------------------------------------------------
        self.cache[key] = False
        return False


# ---------------------------------------------------------
# ITERATIVE DEEPENING (Improvement)
# ---------------------------------------------------------

def iterative_prove(prover, seq):
    for limit in range(1, 25):
        prover.cache.clear()
        prover.fresh_counter = 0

        if prover.prove(seq, depth=0, max_depth=limit, visited=set()):
            return True

    return False