#!/usr/bin/env python3
"""Evaluate the three fixed amplitudes h(z) = (1-z/2)^m, m = 0, 1, 2.

The nodes solve n*theta-psi(theta)=(k-1/2)*pi; the evaluation points solve
n*theta-psi(theta)=k*pi and lie in K=[-0.8,0.8]. Each phase is strictly
increasing because |psi'| <= m < n, so bisection evaluates its unique inverse.
The Lebesgue function uses the derivative-weight identity from Lemma 9.
The correction Lv/v is evaluated from the closed formulas below.

Run: python3 checks/amplitude_numerics.py
Output: the largest corrected value at the prescribed phase midpoints.
"""

import cmath
import math


POWERS = (0, 1, 2)
ROW_SIZES = tuple(range(50, 801, 50))
K = (-0.8, 0.8)
EULER_GAMMA = 0.577215664901532860606512090082402431
VERTESI_CONSTANT = 2 / math.pi * (EULER_GAMMA + math.log(4 / math.pi))


def phase_data(theta, power):
    z = cmath.exp(1j * theta)
    w = 1 - z / 2
    psi = power * cmath.phase(w)
    psi_prime = (-power * z / (2 * w)).real
    return psi, psi_prime, abs(w) ** power


def phase_inverse(target, n, power):
    lo, hi = 0.0, math.pi
    for _ in range(56):
        mid = (lo + hi) / 2
        psi, _, _ = phase_data(mid, power)
        if n * mid - psi < target:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def log_integral_ratio(x, power):
    """Closed expressions for L v(x)/v(x), with v=(5/4-x)^(-m/2)."""
    if power == 0:
        return 0.0
    a = 1.25
    if power == 1:
        b = math.sqrt(a - x)
        return 2 * math.log(
            (math.sqrt(a + 1) + b) * (math.sqrt(a - 1) + b) / (4 * b * b)
        )
    if power == 2:
        return math.log((a * a - 1) / ((a - x) ** 2))
    raise ValueError("The fixed examples have powers 0, 1, and 2.")


def corrected_midpoint_max(n, power):
    nodes, weights = [], []
    for k in range(1, n + 1):
        theta = phase_inverse((k - 0.5) * math.pi, n, power)
        _, psi_prime, modulus = phase_data(theta, power)
        nodes.append(math.cos(theta))
        weights.append(math.sin(theta) / (modulus * (n - psi_prime)))
    values = []
    for k in range(1, n):
        theta = phase_inverse(k * math.pi, n, power)
        x = math.cos(theta)
        if K[0] <= x <= K[1]:
            _, _, modulus = phase_data(theta, power)
            lebesgue = modulus * math.fsum(
                w / abs(x - node) for node, w in zip(nodes, weights)
            )
            values.append(
                lebesgue - 2 / math.pi * math.log(n)
                + log_integral_ratio(x, power) / math.pi
            )
    return max(values)


def main():
    print("h(z): 1, 1-z/2, (1-z/2)^2; K=[-0.8,0.8]")
    print("Maximum over prescribed phase midpoints (floating-point evaluation)")
    print(f"Vertesi constant: {VERTESI_CONSTANT:.12f}")
    print("   n             1           1-z/2       (1-z/2)^2")
    for n in ROW_SIZES:
        values = [corrected_midpoint_max(n, power) for power in POWERS]
        print(f"{n:4d}" + "".join(f"  {value:14.10f}" for value in values))


if __name__ == "__main__":
    main()
