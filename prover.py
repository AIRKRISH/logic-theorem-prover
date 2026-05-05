from copy import deepcopy
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
# PROVER (Algorithm 2 CORRECT BASELINE)
# ---------------------------------------------------------

class Prover:
    def __init__(self):
        self.fresh_counter = 0

    # --------------------------
    # AXIOM CHECK
    # --------------------------
    def is_axiom(self, seq):
        # identity axiom: A appears on both sides
        for l in seq.left:
            for r in seq.right:
                if str(l) == str(r):
                    return True

        # ⊤R and ⊥L (optional if you encode them)
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
    # SUBSTITUTION (safe simple version)
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
    # MAIN PROOF SEARCH (TRUE LK′ BACKWARD SEARCH)
    # ---------------------------------------------------------

    def prove(self, seq, depth=0, max_depth=20):

        if depth > max_depth:
            return False

        # 1. AXIOM
        if self.is_axiom(seq):
            return True

        # -------------------------------------------------
        # 2. NON-BRANCHING RULES (apply ONE at a time)
        # -------------------------------------------------

        # ¬L
        for i, f in enumerate(seq.left):
            if f.type == "NOT":
                new_seq = Sequent(
                    seq.left[:i] + seq.left[i+1:],
                    seq.right + [f.left]
                )
                return self.prove(new_seq, depth + 1)

        # ¬R
        for i, f in enumerate(seq.right):
            if f.type == "NOT":
                new_seq = Sequent(
                    seq.left + [f.left],
                    seq.right[:i] + seq.right[i+1:]
                )
                return self.prove(new_seq, depth + 1)

        # ∧L
        for i, f in enumerate(seq.left):
            if f.type == "AND":
                new_seq = Sequent(
                    seq.left[:i] + seq.left[i+1:] + [f.left, f.right],
                    seq.right
                )
                return self.prove(new_seq, depth + 1)

        # ∨R
        for i, f in enumerate(seq.right):
            if f.type == "OR":
                new_seq = Sequent(
                    seq.left,
                    seq.right[:i] + seq.right[i+1:] + [f.left, f.right]
                )
                return self.prove(new_seq, depth + 1)

        # →R
        for i, f in enumerate(seq.right):
            if f.type == "IMPLIES":
                new_seq = Sequent(
                    seq.left + [f.left],
                    seq.right[:i] + seq.right[i+1:] + [f.right]
                )
                return self.prove(new_seq, depth + 1)

        # -------------------------------------------------
        # 3. BRANCHING RULES (ALL must succeed)
        # -------------------------------------------------

        # ∧R
        for i, f in enumerate(seq.right):
            if f.type == "AND":
                b1 = Sequent(seq.left, seq.right[:i] + seq.right[i+1:] + [f.left])
                b2 = Sequent(seq.left, seq.right[:i] + seq.right[i+1:] + [f.right])
                return self.prove(b1, depth + 1) and self.prove(b2, depth + 1)

        # ∨L
        for i, f in enumerate(seq.left):
            if f.type == "OR":
                b1 = Sequent(seq.left[:i] + seq.left[i+1:] + [f.left], seq.right)
                b2 = Sequent(seq.left[:i] + seq.left[i+1:] + [f.right], seq.right)
                return self.prove(b1, depth + 1) and self.prove(b2, depth + 1)

        # →L
        for i, f in enumerate(seq.left):
            if f.type == "IMPLIES":
                b1 = Sequent(seq.left[:i] + seq.left[i+1:], seq.right + [f.left])
                b2 = Sequent(seq.left[:i] + seq.left[i+1:] + [f.right], seq.right)
                return self.prove(b1, depth + 1) and self.prove(b2, depth + 1)

        # -------------------------------------------------
        # 4. QUANTIFIERS (baseline naive instantiation)
        # -------------------------------------------------

        # ∀R
        for i, f in enumerate(seq.right):
            if f.type == "FORALL":
                t = self.fresh()
                inst = self.substitute(f.left, f.variable, t)
                new_seq = Sequent(
                    seq.left,
                    seq.right[:i] + seq.right[i+1:] + [inst]
                )
                return self.prove(new_seq, depth + 1)

        # ∃L
        for i, f in enumerate(seq.left):
            if f.type == "EXISTS":
                t = self.fresh()
                inst = self.substitute(f.left, f.variable, t)
                new_seq = Sequent(
                    seq.left[:i] + seq.left[i+1:] + [inst],
                    seq.right
                )
                return self.prove(new_seq, depth + 1)
        # ∀L (persist)
        for i, f in enumerate(seq.left):
            if f.type == "FORALL":
                t = self.fresh()
                inst = self.substitute(f.left, f.variable, t)
                return self.prove(Sequent(seq.left + [inst], seq.right), depth + 1)

        # ∃R (persist)
        for i, f in enumerate(seq.right):
            if f.type == "EXISTS":
                t = self.fresh()
                inst = self.substitute(f.left, f.variable, t)
                return self.prove(Sequent(seq.left, seq.right + [inst]), depth + 1)

# ---------------------------------------------------------
# ITERATIVE DEEPENING
# ---------------------------------------------------------

def iterative_prove(prover, seq):
    for limit in range(1, 25):
        if prover.prove(seq, depth=0, max_depth=limit):
            return True
    return False