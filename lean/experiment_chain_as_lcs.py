#!/usr/bin/env python3
"""Experiment: Can we formulate seed chaining as LCS and solve it
with the augmented Krusche comb?

Key idea:
- Seeds = (read_pos, genome_pos) pairs
- Valid chain = increasing subsequence of genome_pos (sorted by read_pos)
- This IS the Longest Increasing Subsequence (LIS) problem
- LIS = LCS of (genome_pos_sequence, sorted_genome_pos_sequence)
- So chaining IS an LCS problem, solvable by the Krusche comb

And with the augmented comb:
- excess = number of "jumps" in the chain (intron crossings)
- correction_score = max(chain_length - go, diagonal_chain_length)
- This is the correction formula applied to chaining!
"""
import itertools


def augmented_comb(a: list[int], b: list[int]) -> tuple:
    """Augmented seaweed comb on integer sequences a (m) and b (n)."""
    m, n = len(a), len(b)
    total = m + n
    labels = list(range(total))
    depths = [0] * total

    for c in range(n):
        for r in range(m):
            t = c - r + m - 1
            if t < 0 or t + 1 >= total:
                continue
            is_match = (a[r] == b[c])
            l_left, l_right = labels[t], labels[t + 1]
            d_left, d_right = depths[t], depths[t + 1]
            if is_match:
                labels[t], labels[t + 1] = l_right, l_left
                depths[t], depths[t + 1] = 0, 0
            elif l_left > l_right:
                labels[t], labels[t + 1] = l_right, l_left
                depths[t], depths[t + 1] = d_right + 1, d_left + 1
            else:
                depths[t], depths[t + 1] = d_left + 1, d_right + 1

    d_col = [labels[m + j] for j in range(n)]
    depth_col = [depths[m + j] for j in range(n)]
    return d_col, depth_col


def lcs_dp(a: list[int], b: list[int]) -> int:
    m, n = len(a), len(b)
    dp = [[0] * (n + 1) for _ in range(m + 1)]
    for i in range(1, m + 1):
        for j in range(1, n + 1):
            if a[i-1] == b[j-1]:
                dp[i][j] = dp[i-1][j-1] + 1
            else:
                dp[i][j] = max(dp[i-1][j], dp[i][j-1])
    return dp[m][n]


def lis_length(seq: list[int]) -> int:
    """LIS via patience sorting, O(n log n)."""
    import bisect
    tails = []
    for x in seq:
        pos = bisect.bisect_left(tails, x)
        if pos == len(tails):
            tails.append(x)
        else:
            tails[pos] = x
    return len(tails)


def chain_dp(seeds: list[tuple[int, int]], gap_cost_fn=None) -> tuple[int, list[int]]:
    """Standard colinear chaining DP with optional gap cost.

    seeds: list of (read_pos, genome_pos) sorted by read_pos
    Returns: (score, chain_indices)
    """
    M = len(seeds)
    if M == 0:
        return 0, []

    dp = [1] * M  # each seed has weight 1
    parent = [-1] * M

    for i in range(1, M):
        for j in range(i):
            if seeds[j][1] < seeds[i][1]:  # genome_pos increasing
                gap = seeds[i][1] - seeds[j][1] - (seeds[i][0] - seeds[j][0])
                if gap_cost_fn:
                    cost = gap_cost_fn(abs(gap)) if gap > 0 else 0
                else:
                    cost = 0
                score = dp[j] + 1 - cost
                if score > dp[i]:
                    dp[i] = score
                    parent[i] = j

    best_i = max(range(M), key=lambda i: dp[i])
    chain = []
    i = best_i
    while i >= 0:
        chain.append(i)
        i = parent[i]
    chain.reverse()

    return dp[best_i], chain


def seeds_to_lcs_problem(seeds: list[tuple[int, int]]) -> tuple[list[int], list[int]]:
    """Convert seed chaining problem to LCS problem.

    A = ranked genome positions (in read order)
    B = identity permutation (sorted order)
    LCS(A, B) = LIS of genome positions = optimal chain length
    """
    g_pos = [s[1] for s in seeds]
    unique_g = sorted(set(g_pos))
    rank = {g: i for i, g in enumerate(unique_g)}

    A = [rank[g] for g in g_pos]
    B = list(range(len(unique_g)))

    return A, B


def diag_matches_chain(seeds: list[tuple[int, int]]) -> int:
    """Count seeds that are on the 'main diagonal' — i.e., seeds where
    the genome position is in the expected order (rank = index).
    These are seeds from the same exon as the first seed."""
    A, B = seeds_to_lcs_problem(seeds)
    return sum(1 for i in range(min(len(A), len(B))) if A[i] == B[i])


def experiment_basic():
    """Basic experiment: does LCS = chain DP (no gap penalty)?"""
    print("=" * 70)
    print("Experiment 1: LCS = Chain DP (no gap penalty)?")
    print("=" * 70)

    # Spliced read: 2 exons
    # Exon 1: read[0:60] → genome[1000:1060]
    # Exon 2: read[60:125] → genome[5000:5065]
    seeds_clean = [
        (0, 1000), (10, 1010), (20, 1020), (30, 1030), (40, 1040), (50, 1050),
        (60, 5000), (70, 5010), (80, 5020), (90, 5030), (100, 5040), (110, 5050),
    ]

    # With noise (false k-mer matches)
    seeds_noisy = seeds_clean + [
        (25, 3000),  # noise seed in middle of genome
        (55, 7000),  # noise seed far away
        (85, 2000),  # noise seed backward (would break chain)
    ]
    seeds_noisy.sort(key=lambda s: s[0])

    for name, seeds in [("Clean (2 exons)", seeds_clean),
                        ("Noisy (2 exons + 3 noise)", seeds_noisy)]:
        print(f"\n--- {name} ---")
        print(f"Seeds: {seeds}")

        # Method 1: Chain DP (no gap penalty)
        chain_score, chain_idx = chain_dp(seeds)
        chain_seeds = [seeds[i] for i in chain_idx]

        # Method 2: LIS of genome positions
        g_pos = [s[1] for s in seeds]
        lis = lis_length(g_pos)

        # Method 3: LCS formulation
        A, B = seeds_to_lcs_problem(seeds)
        lcs = lcs_dp(A, B)

        print(f"Chain DP (no gap):  score={chain_score}, chain={chain_seeds}")
        print(f"LIS:                length={lis}")
        print(f"LCS(A,B):           length={lcs}")
        print(f"Match: LIS == LCS == Chain? {lis == lcs == chain_score}")


def experiment_augmented():
    """Can the augmented comb detect intron jumps in the chain?"""
    print("\n" + "=" * 70)
    print("Experiment 2: Augmented comb detects intron jumps")
    print("=" * 70)

    # Single exon: all seeds on same diagonal
    seeds_single = [
        (0, 1000), (10, 1010), (20, 1020), (30, 1030), (40, 1040),
        (50, 1050), (60, 1060), (70, 1070), (80, 1080), (90, 1090),
    ]

    # Two exons: jump at seed 5→6
    seeds_spliced = [
        (0, 1000), (10, 1010), (20, 1020), (30, 1030), (40, 1040),
        (50, 5000), (60, 5010), (70, 5020), (80, 5030), (90, 5040),
    ]

    # Three exons: jumps at 3→4 and 6→7
    seeds_triple = [
        (0, 1000), (10, 1010), (20, 1020),
        (30, 3000), (40, 3010), (50, 3020),
        (60, 7000), (70, 7010), (80, 7020),
    ]

    for name, seeds in [("Single exon", seeds_single),
                        ("Two exons (1 junction)", seeds_spliced),
                        ("Three exons (2 junctions)", seeds_triple)]:
        print(f"\n--- {name} ---")

        A, B = seeds_to_lcs_problem(seeds)
        lcs = lcs_dp(A, B)

        # Diagonal matches: seeds where rank(g_i) == i
        diag = sum(1 for i in range(min(len(A), len(B))) if A[i] == B[i])
        excess = lcs - diag

        # Run augmented comb
        d_col, depth_col = augmented_comb(A, B)

        # Correction score at various go values
        print(f"LCS (chain length):     {lcs}")
        print(f"Diagonal (same-exon):   {diag}")
        print(f"Excess (intron jumps):   {excess}")
        print(f"A = {A}")
        print(f"B = {B}")
        print(f"depth_col = {depth_col[:len(A)]}")

        for go in [0, 1, 2, 3, 5]:
            corr = max(lcs - go, diag)
            print(f"  go={go}: correction = max({lcs}-{go}, {diag}) = {corr}")


def experiment_gap_penalty():
    """Does the correction formula on chains reproduce gap-penalized chaining?"""
    print("\n" + "=" * 70)
    print("Experiment 3: Correction formula vs gap-penalized chain DP")
    print("=" * 70)

    import math

    def log_gap_cost(gap):
        if gap <= 0:
            return 0
        return 2 + math.log2(max(1, gap))

    # Seeds with varying intron sizes
    test_cases = [
        ("Small intron (100bp)", [
            (0, 1000), (10, 1010), (20, 1020), (30, 1030), (40, 1040),
            (50, 1100+50), (60, 1100+60), (70, 1100+70), (80, 1100+80), (90, 1100+90),
        ]),
        ("Medium intron (10Kbp)", [
            (0, 1000), (10, 1010), (20, 1020), (30, 1030), (40, 1040),
            (50, 11000+50), (60, 11000+60), (70, 11000+70), (80, 11000+80), (90, 11000+90),
        ]),
        ("Large intron (1Mbp)", [
            (0, 1000), (10, 1010), (20, 1020), (30, 1030), (40, 1040),
            (50, 1001000+50), (60, 1001000+60), (70, 1001000+70), (80, 1001000+80), (90, 1001000+90),
        ]),
        ("No intron (single exon)", [
            (0, 1000), (10, 1010), (20, 1020), (30, 1030), (40, 1040),
            (50, 1050), (60, 1060), (70, 1070), (80, 1080), (90, 1090),
        ]),
    ]

    for name, seeds in test_cases:
        print(f"\n--- {name} ---")

        # Chain DP with gap penalty
        gap_score, gap_chain = chain_dp(seeds, gap_cost_fn=log_gap_cost)

        # Chain DP without gap penalty
        nogap_score, nogap_chain = chain_dp(seeds)

        # LCS formulation
        A, B = seeds_to_lcs_problem(seeds)
        lcs = lcs_dp(A, B)
        diag = sum(1 for i in range(min(len(A), len(B))) if A[i] == B[i])
        excess = lcs - diag

        print(f"Chain DP (no gap):      score={nogap_score}")
        print(f"Chain DP (log gap):     score={gap_score:.1f}")
        print(f"LCS = LIS:              {lcs}")
        print(f"Excess (intron jumps):   {excess}")
        print(f"Correction (go=1):      {max(lcs - 1, diag)}")
        print(f"Correction (go=2):      {max(lcs - 2, diag)}")

        # Key question: same chain selected?
        gap_seeds = [seeds[i] for i in gap_chain]
        nogap_seeds = [seeds[i] for i in nogap_chain]
        print(f"Same chain? {gap_seeds == nogap_seeds}")


def experiment_noise_rejection():
    """Does the correction formula naturally reject noise seeds?"""
    print("\n" + "=" * 70)
    print("Experiment 4: Noise rejection via correction formula")
    print("=" * 70)

    # True chain: 10 seeds on 2 exons
    # Noise: 5 random seeds scattered across genome
    import random
    random.seed(42)

    true_seeds = [
        (0, 1000), (10, 1010), (20, 1020), (30, 1030), (40, 1040),
        (50, 5000), (60, 5010), (70, 5020), (80, 5030), (90, 5040),
    ]

    noise_seeds = [(random.randint(0, 90), random.randint(0, 10000)) for _ in range(5)]

    all_seeds = sorted(true_seeds + noise_seeds, key=lambda s: s[0])

    print(f"True seeds: {true_seeds}")
    print(f"Noise seeds: {noise_seeds}")
    print(f"All seeds (sorted): {all_seeds}")

    # LIS on all seeds
    g_pos = [s[1] for s in all_seeds]
    lis = lis_length(g_pos)

    # LCS formulation
    A, B = seeds_to_lcs_problem(all_seeds)
    lcs = lcs_dp(A, B)
    diag = sum(1 for i in range(min(len(A), len(B))) if A[i] == B[i])
    excess = lcs - diag

    print(f"\nLIS (chain length): {lis}")
    print(f"LCS: {lcs}")
    print(f"Diagonal: {diag}")
    print(f"Excess: {excess}")
    print(f"Correction (go=2): {max(lcs - 2, diag)}")

    # Compare with true seeds only
    A_true, B_true = seeds_to_lcs_problem(true_seeds)
    lcs_true = lcs_dp(A_true, B_true)
    diag_true = sum(1 for i in range(min(len(A_true), len(B_true))) if A_true[i] == B_true[i])
    excess_true = lcs_true - diag_true

    print(f"\nTrue seeds only:")
    print(f"  LCS: {lcs_true}, diag: {diag_true}, excess: {excess_true}")
    print(f"  Correction (go=2): {max(lcs_true - 2, diag_true)}")


if __name__ == "__main__":
    experiment_basic()
    experiment_augmented()
    experiment_gap_penalty()
    experiment_noise_rejection()
