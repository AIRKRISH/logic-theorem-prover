from prover import Prover, iterative_prove
from parser import parse_formula
from prover import Sequent  # if Sequent is in prover file


# ---------------------------------------------------------
# TEST CASES
# ---------------------------------------------------------

tests = [
    # Propositional logic test (should be VALID)
    "(P -> Q) -> (~Q -> ~P)",

    # Simple valid identity
    "P -> P",

    # Conjunction test
    "(P & Q) -> P",

    # Quantifier test (important for assignment)
    "forall x P(x) -> P(a)",

    # Slightly harder quantifier test
    "exists x P(x) -> exists x P(x)",
]


# ---------------------------------------------------------
# RUN TESTS
# ---------------------------------------------------------

def run_tests():
    prover = Prover()

    for i, formula_str in enumerate(tests, 1):
        print("\n-----------------------------------")
        print(f"TEST {i}: {formula_str}")

        try:
            formula = parse_formula(formula_str)
            seq = Sequent([], [formula])

            result = iterative_prove(prover, seq)

            print("RESULT:", "VALID (provable)" if result else "NOT PROVABLE")

        except Exception as e:
            print("ERROR:", e)


# ---------------------------------------------------------
# MAIN
# ---------------------------------------------------------

if __name__ == "__main__":
    run_tests()