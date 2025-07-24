import argparse
from itertools import combinations


def find_sunflower(supports, t):
    """Return core and subset forming t-sunflower if one exists."""
    for comb in combinations(supports, t):
        core = set.intersection(*comb)
        if all(A & B == core for A in comb for B in comb if A is not B):
            return core, list(comb)
    return None


def main():
    parser = argparse.ArgumentParser(description="Find a sunflower in a set of supports")
    parser.add_argument("--t", type=int, default=3, help="sunflower size (number of petals)")
    parser.add_argument("supports", nargs="+", help="Supports as comma-separated lists of integers")
    args = parser.parse_args()

    supp_sets = [set(map(int, s.split(','))) for s in args.supports]
    result = find_sunflower(supp_sets, args.t)
    if result is None:
        print("No sunflower found")
    else:
        core, petals = result
        print(f"Core: {sorted(core)}")
        print("Petals:")
        for p in petals:
            print(sorted(p))


if __name__ == "__main__":
    main()
