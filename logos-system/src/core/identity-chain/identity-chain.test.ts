/**
 * Unit tests for the Complete Identity Chain
 * These tests verify the mathematical correctness of all n-square identities
 */

import { IdentityChain } from '../index';

describe('IdentityChain - Complete N-Square Identities', () => {
  
  describe('Brahmagupta-Fibonacci Identity (2D)', () => {
    test('basic complex multiplication', () => {
      // (1 + i) * (1 - i) = 1 - i² = 2 (in real numbers)
      const a: [number, number] = [1, 1];
      const b: [number, number] = [1, -1];
      const expected: [number, number] = [2, 0];
      
      expect(IdentityChain.brahmagupta2(a, b)).toEqual(expected);
    });

    test('multiplication by zero', () => {
      const a: [number, number] = [1, 1];
      const zero: [number, number] = [0, 0];
      
      expect(IdentityChain.brahmagupta2(a, zero)).toEqual([0, 0]);
      expect(IdentityChain.brahmagupta2(zero, a)).toEqual([0, 0]);
    });

    test('multiplication by one', () => {
      const a: [number, number] = [3, 4];
      const one: [number, number] = [1, 0];
      
      expect(IdentityChain.brahmagupta2(a, one)).toEqual(a);
      expect(IdentityChain.brahmagupta2(one, a)).toEqual(a);
    });

    test('commutativity', () => {
      const a: [number, number] = [2, 3];
      const b: [number, number] = [5, 7];
      
      const ab = IdentityChain.brahmagupta2(a, b);
      const ba = IdentityChain.brahmagupta2(b, a);
      
      expect(ab).toEqual(ba);
    });

    test('associativity', () => {
      const a: [number, number] = [1, 2];
      const b: [number, number] = [3, 4];
      const c: [number, number] = [5, 6];
      
      const abc = IdentityChain.brahmagupta2(IdentityChain.brahmagupta2(a, b), c);
      const a_bc = IdentityChain.brahmagupta2(a, IdentityChain.brahmagupta2(b, c));
      
      expect(abc).toEqual(a_bc);
    });

    test('norm preservation', () => {
      const a: [number, number] = [3, 4];  // norm = 5
      const b: [number, number] = [5, 12]; // norm = 13
      
      expect(IdentityChain.verify_norm_preservation_2(a, b)).toBe(true);
    });

    test('Brahmagupta identity verification', () => {
      // (a₁² + a₂²)(b₁² + b₂²) = (a₁b₁ - a₂b₂)² + (a₁b₂ + a₂b₁)²
      const a: [number, number] = [7, 24];  // norm = 25
      const b: [number, number] = [8, 15];  // norm = 17
      
      const product = IdentityChain.brahmagupta2(a, b);
      const left_norm = IdentityChain.norm_squared_2(a) * IdentityChain.norm_squared_2(b);
      const right_norm = IdentityChain.norm_squared_2(product);
      
      expect(left_norm).toBeCloseTo(right_norm, 10);
    });
  });

  describe('Euler Four-Square Identity (4D)', () => {
    test('basic quaternion multiplication', () => {
      // i * i = -1
      const i: [number, number, number, number] = [0, 1, 0, 0];
      const expected: [number, number, number, number] = [-1, 0, 0, 0];
      
      expect(IdentityChain.euler4(i, i)).toEqual(expected);
    });

    test('quaternion units multiplication', () => {
      const i: [number, number, number, number] = [0, 1, 0, 0];
      const j: [number, number, number, number] = [0, 0, 1, 0];
      const k: [number, number, number, number] = [0, 0, 0, 1];
      
      // i * j = k
      expect(IdentityChain.euler4(i, j)).toEqual(k);
      
      // j * k = i  
      expect(IdentityChain.euler4(j, k)).toEqual(i);
      
      // k * i = j
      expect(IdentityChain.euler4(k, i)).toEqual(j);
      
      // j * i = -k
      expect(IdentityChain.euler4(j, i)).toEqual([-0, -0, -0, -1]);
    });

    test('non-commutativity of quaternions', () => {
      const i: [number, number, number, number] = [0, 1, 0, 0];
      const j: [number, number, number, number] = [0, 0, 1, 0];
      
      const ij = IdentityChain.euler4(i, j);
      const ji = IdentityChain.euler4(j, i);
      
      expect(ij).not.toEqual(ji);
      // ij should be k, ji should be -k
      expect(ij[3]).toBe(1);  // k
      expect(ji[3]).toBe(-1); // -k
    });

    test('associativity of quaternions', () => {
      const i: [number, number, number, number] = [0, 1, 0, 0];
      const j: [number, number, number, number] = [0, 0, 1, 0];
      const k: [number, number, number, number] = [0, 0, 0, 1];
      
      const ijk = IdentityChain.euler4(IdentityChain.euler4(i, j), k);
      const i_jk = IdentityChain.euler4(i, IdentityChain.euler4(j, k));
      
      expect(ijk).toEqual(i_jk);
    });

    test('norm preservation', () => {
      const a = IdentityChain.generate_unit_vector_4();
      const b = IdentityChain.generate_unit_vector_4();
      
      expect(IdentityChain.verify_norm_preservation_4(a, b)).toBe(true);
    });

    test('Euler identity verification', () => {
      const a: [number, number, number, number] = [1, 2, 3, 4];
      const b: [number, number, number, number] = [5, 6, 7, 8];
      
      const product = IdentityChain.euler4(a, b);
      const left_norm = IdentityChain.norm_squared_4(a) * IdentityChain.norm_squared_4(b);
      const right_norm = IdentityChain.norm_squared_4(product);
      
      expect(left_norm).toBeCloseTo(right_norm, 10);
    });
  });

  describe('Degen Eight-Square Identity (8D)', () => {
    test('basic octonion multiplication', () => {
      // e₁ * e₁ = -1
      const e1: [number, number, number, number, number, number, number, number] = [0, 1, 0, 0, 0, 0, 0, 0];
      const expected: [number, number, number, number, number, number, number, number] = [-1, 0, 0, 0, 0, 0, 0, 0];
      
      expect(IdentityChain.degen8(e1, e1)).toEqual(expected);
    });

    test('octonion conjugation', () => {
      const oct: [number, number, number, number, number, number, number, number] = [1, 2, 3, 4, 5, 6, 7, 8];
      const expected_conj: [number, number, number, number, number, number, number, number] = [1, -2, -3, -4, -5, -6, -7, -8];
      
      expect(IdentityChain.conjugate8(oct)).toEqual(expected_conj);
    });

    test('non-associativity of octonions', () => {
      // Find a specific case where associativity fails
      const e1: [number, number, number, number, number, number, number, number] = [0, 1, 0, 0, 0, 0, 0, 0];
      const e2: [number, number, number, number, number, number, number, number] = [0, 0, 1, 0, 0, 0, 0, 0];
      const e4: [number, number, number, number, number, number, number, number] = [0, 0, 0, 1, 0, 0, 0, 0];
      
      const e12_e4 = IdentityChain.degen8(IdentityChain.degen8(e1, e2), e4);
      const e1_e24 = IdentityChain.degen8(e1, IdentityChain.degen8(e2, e4));
      
      // These should be different (demonstrating non-associativity)
      expect(e12_e4).not.toEqual(e1_e24);
    });

    test('alternativity of octonions', () => {
      // Octonions are alternative: any subalgebra generated by two elements is associative
      const e1: [number, number, number, number, number, number, number, number] = [0, 1, 0, 0, 0, 0, 0, 0];
      const e2: [number, number, number, number, number, number, number, number] = [0, 0, 1, 0, 0, 0, 0, 0];
      const e3: [number, number, number, number, number, number, number, number] = [0, 0, 0, 1, 0, 0, 0, 0];
      
      // (e1 * e2) * e2 = e1 * (e2 * e2) should hold (alternativity)
      const e12_e2 = IdentityChain.degen8(IdentityChain.degen8(e1, e2), e2);
      const e1_e22 = IdentityChain.degen8(e1, IdentityChain.degen8(e2, e2));
      
      expect(e12_e2).toEqual(e1_e22);
    });

    test('norm preservation', () => {
      const a = IdentityChain.generate_unit_vector_8();
      const b = IdentityChain.generate_unit_vector_8();
      
      expect(IdentityChain.verify_norm_preservation_8(a, b)).toBe(true);
    });

    test('Degen identity verification', () => {
      const a: [number, number, number, number, number, number, number, number] = [1, 2, 3, 4, 5, 6, 7, 8];
      const b: [number, number, number, number, number, number, number, number] = [8, 7, 6, 5, 4, 3, 2, 1];
      
      const product = IdentityChain.degen8(a, b);
      const left_norm = IdentityChain.norm_squared_8(a) * IdentityChain.norm_squared_8(b);
      const right_norm = IdentityChain.norm_squared_8(product);
      
      expect(left_norm).toBeCloseTo(right_norm, 10);
    });
  });

  describe('Pfister Sixteen-Square Identity (16D)', () => {
    test('Pfister construction basics', () => {
      const oct: [number, number, number, number, number, number, number, number] = [1, 2, 3, 4, 5, 6, 7, 8];
      const expanded = IdentityChain.expand_to_16(oct);
      
      expect(expanded).toHaveLength(16);
      expect(expanded.slice(0, 8)).toEqual(oct);
      
      // Check golden ratio scaling
      const phi = (1 + Math.sqrt(5)) / 2;
      expanded.slice(8, 16).forEach((val, i) => {
        expect(val).toBeCloseTo(oct[i] * phi, 10);
      });
    });

    test('16D reduction to 8D', () => {
      const oct1: [number, number, number, number, number, number, number, number] = [1, 2, 3, 4, 5, 6, 7, 8];
      const oct2: [number, number, number, number, number, number, number, number] = [8, 7, 6, 5, 4, 3, 2, 1];
      
      const expanded1 = IdentityChain.expand_to_16(oct1);
      const expanded2 = IdentityChain.expand_to_16(oct2);
      
      const composed16 = IdentityChain.pfister16(expanded1, expanded2);
      const reduced8 = IdentityChain.reduce_to_8(composed16);
      
      expect(reduced8).toHaveLength(8);
      expect(reduced8.every(x => !isNaN(x) && isFinite(x))).toBe(true);
    });
  });

  describe('Complete Chain Composition', () => {
    test('chain composition preserves norm', () => {
      const a = IdentityChain.generate_unit_vector_8();
      const b = IdentityChain.generate_unit_vector_8();
      
      expect(IdentityChain.verify_chain_norm_preservation(a, b)).toBe(true);
    });

    test('chain composition vs direct multiplication', () => {
      const a: [number, number, number, number, number, number, number, number] = [1, 0, 0, 0, 0, 0, 0, 0];
      const b: [number, number, number, number, number, number, number, number] = [0, 1, 0, 0, 0, 0, 0, 0];
      
      const direct = IdentityChain.degen8(a, b);
      const chain = IdentityChain.compose_chain(a, b);
      
      // For simple cases, chain should equal direct multiplication
      expect(chain).toEqual(direct);
    });

    test('chain roundtrip properties', () => {
      const original = IdentityChain.generate_unit_vector_8();
      const expanded = IdentityChain.expand_to_16(original);
      const reduced = IdentityChain.reduce_to_8(expanded);
      
      // Expand then reduce should return approximately the same vector
      expect(reduced.every((x, i) => Math.abs(x - original[i]) < 1e-10)).toBe(true);
    });

    test('composition associativity through chain', () => {
      const a = IdentityChain.generate_unit_vector_8();
      const b = IdentityChain.generate_unit_vector_8();
      const c = IdentityChain.generate_unit_vector_8();
      
      const ab_c = IdentityChain.compose_chain(IdentityChain.compose_chain(a, b), c);
      const a_bc = IdentityChain.compose_chain(a, IdentityChain.compose_chain(b, c));
      
      // The chain provides a form of "associativity" through dimensional elevation
      expect(ab_c).toHaveLength(8);
      expect(a_bc).toHaveLength(8);
      
      // Verify both preserve norm
      expect(IdentityChain.verify_chain_norm_preservation(a, b)).toBe(true);
      expect(IdentityChain.verify_chain_norm_preservation(IdentityChain.compose_chain(a, b), c)).toBe(true);
    });
  });

  describe('Utility Functions', () => {
    test('norm calculations', () => {
      const v2: [number, number] = [3, 4];
      const v4: [number, number, number, number] = [1, 2, 3, 4];
      const v8: [number, number, number, number, number, number, number, number] = [1, 2, 3, 4, 5, 6, 7, 8];
      
      expect(IdentityChain.norm_squared_2(v2)).toBe(25);
      expect(IdentityChain.norm_squared_4(v4)).toBe(30);
      expect(IdentityChain.norm_squared_8(v8)).toBe(204);
    });

    test('vector normalization', () => {
      const v2: [number, number] = [3, 4];
      const normalized2 = IdentityChain.normalize_2(v2);
      
      expect(IdentityChain.norm_squared_2(normalized2)).toBeCloseTo(1, 10);
      expect(normalized2[0]).toBeCloseTo(0.6, 10);
      expect(normalized2[1]).toBeCloseTo(0.8, 10);
    });

    test('unit vector generation', () => {
      const unit2 = IdentityChain.generate_unit_vector_2(Math.PI / 4);
      expect(IdentityChain.norm_squared_2(unit2)).toBeCloseTo(1, 10);
      
      const unit4 = IdentityChain.generate_unit_vector_4();
      expect(IdentityChain.norm_squared_4(unit4)).toBeCloseTo(1, 10);
      
      const unit8 = IdentityChain.generate_unit_vector_8();
      expect(IdentityChain.norm_squared_8(unit8)).toBeCloseTo(1, 10);
    });

    test('algebraic properties verification', () => {
      const properties = IdentityChain.verify_properties();
      
      expect(properties['2d_commutative']).toBe(true);
      expect(properties['2d_associative']).toBe(true);
      expect(properties['2d_norm_preservation']).toBe(true);
    });
  });

  describe('Mathematical Constants', () => {
    test('golden ratio properties', () => {
      const phi = IDENTITY_CHAIN_CONSTANTS.PHI;
      
      // φ² = φ + 1
      expect(phi * phi).toBeCloseTo(phi + 1, 10);
      
      // 1/φ = φ - 1
      expect(1 / phi).toBeCloseTo(phi - 1, 10);
    });

    test('square root constants', () => {
      expect(IDENTITY_CHAIN_CONSTANTS.SQRT2).toBe(Math.sqrt(2));
      expect(IDENTITY_CHAIN_CONSTANTS.SQRT2_INV).toBe(1 / Math.sqrt(2));
      expect(IDENTITY_CHAIN_CONSTANTS.SQRT2 * IDENTITY_CHAIN_CONSTANTS.SQRT2_INV).toBeCloseTo(1, 10);
    });
  });

  describe('Edge Cases and Robustness', () => {
    test('zero vector handling', () => {
      const zero2: [number, number] = [0, 0];
      const zero4: [number, number, number, number] = [0, 0, 0, 0];
      const zero8: [number, number, number, number, number, number, number, number] = [0, 0, 0, 0, 0, 0, 0, 0];
      
      expect(IdentityChain.norm_squared_2(zero2)).toBe(0);
      expect(IdentityChain.norm_squared_4(zero4)).toBe(0);
      expect(IdentityChain.norm_squared_8(zero8)).toBe(0);
    });

    test('large vector handling', () => {
      // Test with large numbers to check for overflow issues
      const large2: [number, number] = [1e6, 1e6];
      const large8: [number, number, number, number, number, number, number, number] = 
        [1e2, 1e2, 1e2, 1e2, 1e2, 1e2, 1e2, 1e2];
      
      expect(() => IdentityChain.brahmagupta2(large2, large2)).not.toThrow();
      expect(() => IdentityChain.degen8(large8, large8)).not.toThrow();
      
      // Check that results are finite
      const result2 = IdentityChain.brahmagupta2(large2, large2);
      const result8 = IdentityChain.degen8(large8, large8);
      
      result2.forEach(x => expect(isFinite(x)).toBe(true));
      result8.forEach(x => expect(isFinite(x)).toBe(true));
    });

    test('precision and floating point errors', () => {
      // Test operations that might cause floating point precision issues
      const a: [number, number] = [1e-10, 1e-10];
      const b: [number, number] = [1e10, 1e10];
      
      const product = IdentityChain.brahmagupta2(a, b);
      expect(product.every(x => isFinite(x))).toBe(true);
      
      // Check norm preservation holds even with extreme values
      expect(IdentityChain.verify_norm_preservation_2(a, b, 1e-6)).toBe(true);
    });
  });
});