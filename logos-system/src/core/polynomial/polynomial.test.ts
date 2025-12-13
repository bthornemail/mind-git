/**
 * Unit tests for Polynomial Algebra over F₂
 * These tests will be formally verified against Coq proofs
 */

import { PolyF2 } from '../index';

describe('PolyF2 - Polynomial Algebra over F₂', () => {
  
  describe('Basic Operations', () => {
    test('degree calculation', () => {
      expect(PolyF2.degree([])).toBe(-1); // zero polynomial
      expect(PolyF2.degree([true])).toBe(0); // 1
      expect(PolyF2.degree([false, true])).toBe(1); // x
      expect(PolyF2.degree([true, false, true])).toBe(2); // 1 + x²
    });

    test('trim removes leading zeros', () => {
      expect(PolyF2.trim([false, false, true, false])).toEqual([true]);
      expect(PolyF2.trim([false, false])).toEqual([]);
      expect(PolyF2.trim([true, false, false])).toEqual([true]);
    });

    test('zero polynomial detection', () => {
      expect(PolyF2.is_zero([])).toBe(true);
      expect(PolyF2.is_zero([false])).toBe(true);
      expect(PolyF2.is_zero([true])).toBe(false);
      expect(PolyF2.is_zero([false, true])).toBe(false);
    });
  });

  describe('Addition (XOR)', () => {
    test('simple addition', () => {
      // (1 + x²) + (1 + x) = x + x²
      const a = [true, false, true];    // 1 + x²
      const b = [true, true, false];    // 1 + x  
      const expected = [false, true, true]; // x + x²
      
      expect(PolyF2.add(a, b)).toEqual(expected);
    });

    test('additive identity', () => {
      const p = [true, false, true];
      expect(PolyF2.add(p, [])).toEqual(p);
      expect(PolyF2.add([], p)).toEqual(p);
    });

    test('additive inverse', () => {
      const p = [true, false, true];
      expect(PolyF2.add(p, p)).toEqual([]); // p + p = 0 in F₂
    });

    test('commutativity', () => {
      const a = [true, false, true];
      const b = [false, true, false];
      
      const ab = PolyF2.add(a, b);
      const ba = PolyF2.add(b, a);
      
      expect(ab).toEqual(ba);
    });

    test('associativity', () => {
      const a = [true, false, false];
      const b = [false, true, false];
      const c = [false, false, true];
      
      const abc = PolyF2.add(PolyF2.add(a, b), c);
      const a_bc = PolyF2.add(a, PolyF2.add(b, c));
      
      expect(abc).toEqual(a_bc);
    });
  });

  describe('Multiplication (Convolution)', () => {
    test('simple multiplication', () => {
      // (x + 1) * (x² + 1) = x³ + x² + x + 1
      const a = [true, true];           // 1 + x
      const b = [true, false, true];    // 1 + x²
      const expected = [true, true, true, true]; // 1 + x + x² + x³
      
      expect(PolyF2.mul(a, b)).toEqual(expected);
    });

    test('multiplication by zero', () => {
      const p = [true, false, true];
      expect(PolyF2.mul(p, [])).toEqual([]);
      expect(PolyF2.mul([], p)).toEqual([]);
    });

    test('multiplication by one', () => {
      const p = [true, false, true];
      const one = [true];
      expect(PolyF2.mul(p, one)).toEqual(p);
      expect(PolyF2.mul(one, p)).toEqual(p);
    });

    test('commutativity', () => {
      const a = [true, false, true];
      const b = [false, true, false];
      
      const ab = PolyF2.mul(a, b);
      const ba = PolyF2.mul(b, a);
      
      expect(ab).toEqual(ba);
    });

    test('distributivity over addition', () => {
      const a = [true, false];          // 1 + x
      const b = [false, true];          // x
      const c = [true, true];           // 1 + x
      
      // a * (b + c) = a*b + a*c
      const left = PolyF2.mul(a, PolyF2.add(b, c));
      const right = PolyF2.add(PolyF2.mul(a, b), PolyF2.mul(a, c));
      
      expect(left).toEqual(right);
    });
  });

  describe('Division with Remainder', () => {
    test('exact division', () => {
      // (x³ + x² + x + 1) / (x + 1) = x² + 1
      const dividend = [true, true, true, true];  // 1 + x + x² + x³
      const divisor = [true, true];               // 1 + x
      const expected_quotient = [true, false, true]; // 1 + x²
      const expected_remainder: boolean[] = [];    // 0
      
      const [quotient, remainder] = PolyF2.divmod(dividend, divisor);
      
      expect(quotient).toEqual(expected_quotient);
      expect(remainder).toEqual(expected_remainder);
    });

    test('division with remainder', () => {
      // (x² + x) / (x + 1) = x with remainder 1
      const dividend = [false, true, true];    // x + x²
      const divisor = [true, true];            // 1 + x
      const expected_quotient = [false, true]; // x
      const expected_remainder = [true];       // 1
      
      const [quotient, remainder] = PolyF2.divmod(dividend, divisor);
      
      expect(quotient).toEqual(expected_quotient);
      expect(remainder).toEqual(expected_remainder);
    });

    test('division by zero throws error', () => {
      expect(() => {
        PolyF2.divmod([true], []);
      }).toThrow('Division by zero polynomial');
    });
  });

  describe('Greatest Common Divisor', () => {
    test('gcd with zero polynomial', () => {
      const p = [true, false, true];
      expect(PolyF2.gcd(p, [])).toEqual(p);
      expect(PolyF2.gcd([], p)).toEqual(p);
    });

    test('gcd of coprime polynomials', () => {
      // gcd(x + 1, x² + x + 1) = 1
      const a = [true, true];           // 1 + x
      const b = [true, true, true];     // 1 + x + x²
      const expected = [true];          // 1
      
      expect(PolyF2.gcd(a, b)).toEqual(expected);
    });

    test('gcd with common factor', () => {
      // gcd(x² + 1, x⁴ + 1) = x² + 1
      const a = [true, false, true];           // 1 + x²
      const b = [true, false, false, false, true]; // 1 + x⁴
      const expected = [true, false, true];     // 1 + x²
      
      expect(PolyF2.gcd(a, b)).toEqual(expected);
    });
  });

  describe('Shift Operations', () => {
    test('left shift', () => {
      const p = [true, false];    // 1
      const shifted = PolyF2.shift_left(p, 3); // x³
      const expected = [false, false, false, true];
      
      expect(shifted).toEqual(expected);
    });

    test('right shift', () => {
      const p = [false, false, false, true]; // x³
      const shifted = PolyF2.shift_right(p, 3); // 1
      const expected = [true];
      
      expect(shifted).toEqual(expected);
    });

    test('shift by zero returns original', () => {
      const p = [true, false, true];
      expect(PolyF2.shift_left(p, 0)).toEqual(p);
      expect(PolyF2.shift_right(p, 0)).toEqual(p);
    });
  });

  describe('Utility Functions', () => {
    test('toInteger conversion', () => {
      expect(PolyF2.toInteger([true])).toBe(1);
      expect(PolyF2.toInteger([false, true])).toBe(2);
      expect(PolyF2.toInteger([true, true])).toBe(3);
      expect(PolyF2.toInteger([true, false, true])).toBe(5);
    });

    test('fromInteger conversion', () => {
      expect(PolyF2.fromInteger(1)).toEqual([true]);
      expect(PolyF2.fromInteger(2)).toEqual([false, true]);
      expect(PolyF2.fromInteger(3)).toEqual([true, true]);
      expect(PolyF2.fromInteger(5)).toEqual([true, false, true]);
    });

    test('integer conversion roundtrip', () => {
      for (let i = 0; i < 100; i++) {
        const p = PolyF2.fromInteger(i);
        const roundtrip = PolyF2.toInteger(p);
        expect(roundtrip).toBe(i);
      }
    });

    test('string representation', () => {
      expect(PolyF2.toString([])).toBe("0");
      expect(PolyF2.toString([true])).toBe("1");
      expect(PolyF2.toString([false, true])).toBe("x");
      expect(PolyF2.toString([true, false, true])).toBe("1 + x^2");
      expect(PolyF2.toString([true, true, true])).toBe("1 + x + x^2");
    });

    test('evaluate at x = 1', () => {
      // Count of true coefficients mod 2
      expect(PolyF2.evaluate_at_1([])).toBe(false);     // 0 coefficients
      expect(PolyF2.evaluate_at_1([true])).toBe(true);  // 1 coefficient
      expect(PolyF2.evaluate_at_1([true, true])).toBe(false); // 2 coefficients
      expect(PolyF2.evaluate_at_1([true, true, true])).toBe(true); // 3 coefficients
    });
  });

  describe('Mathematical Properties', () => {
    test('norm multiplication property', () => {
      // For polynomials over F₂, the "norm" is the number of non-zero coefficients
      // This isn't preserved under multiplication, but we test consistency
      
      const a = [true, false, true];
      const b = [true, true];
      const product = PolyF2.mul(a, b);
      
      // Product degree should be sum of degrees (unless cancellation occurs)
      const expected_degree = PolyF2.degree(a) + PolyF2.degree(b);
      const actual_degree = PolyF2.degree(product);
      
      expect(actual_degree).toBeLessThanOrEqual(expected_degree);
    });

    test('field axioms verification', () => {
      const polynomials = [
        [],
        [true],
        [false, true],
        [true, false, true],
        [true, true, false, true]
      ];

      // Test that F₂[x] forms a ring (not a field due to zero divisors)
      for (const a of polynomials) {
        for (const b of polynomials) {
          // Commutativity of addition and multiplication
          expect(PolyF2.add(a, b)).toEqual(PolyF2.add(b, a));
          expect(PolyF2.mul(a, b)).toEqual(PolyF2.mul(b, a));
          
          // Distributivity
          const c = [true, false]; // Test element
          expect(PolyF2.mul(a, PolyF2.add(b, c))).toEqual(
            PolyF2.add(PolyF2.mul(a, b), PolyF2.mul(a, c))
          );
        }
      }
    });
  });

  describe('Edge Cases', () => {
    test('large polynomials', () => {
      // Test with degree 100 polynomials
      const a = Array.from({length: 50}, (_, i) => i % 2 === 0);
      const b = Array.from({length: 50}, (_, i) => i % 3 === 0);
      
      // Should not throw errors
      const sum = PolyF2.add(a, b);
      const product = PolyF2.mul(a, b);
      
      expect(sum.length).toBeLessThanOrEqual(50);
      expect(product.length).toBeLessThanOrEqual(99); // 49 + 49
    });

    test('empty polynomial edge cases', () => {
      const empty: boolean[] = [];
      
      expect(PolyF2.add(empty, empty)).toEqual(empty);
      expect(PolyF2.mul(empty, empty)).toEqual(empty);
      expect(PolyF2.gcd(empty, empty)).toEqual(empty);
      expect(PolyF2.degree(empty)).toBe(-1);
    });
  });
});