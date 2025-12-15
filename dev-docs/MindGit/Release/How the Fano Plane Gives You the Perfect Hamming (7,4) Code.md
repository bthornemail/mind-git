---
id: "mind-git:development:how-the-fano-plane-gives-you-the-perfect-hamming--7-4--code"
title: "In the MindGit repo"
type: ["development"]
category: development
layer: 7
dimensions: [3, 4, 5]
mathematicalFoundation: ["general"]
hopfCompatible: false
normPreserving: false
status: "complete"
completeness: 80
tags: ["development","documentation","canvasl","mathematics","ast"]
keywords: ["canvasl","ast"]
lastUpdate: "2025-12-15"

---

### How the Fano Plane Gives You the Perfect Hamming (7,4) Code  
(And why CanvasL / MindGit use it as a built-in error-correction layer)

The Hamming (7,4) code is the most famous **perfect single-error-correcting code**:  
- 4 data bits → 7 transmitted bits  
- Can correct **any single bit flip**  
- Can detect **any two bit flips**  
- It is **perfect** — it achieves the absolute theoretical maximum number of codewords for its length and distance (Hamming bound is met with equality).

The astonishing fact: **the entire code is literally the Fano plane**.

#### The 16 Codewords = The 16 Possible 3-Bit Vectors (Including 000)

Think of the 7 points of the Fano plane as the **7 bit positions** in the 7-bit word:

```
Position:   1 2 3 4 5 6 7
```

Every line in the Fano plane tells you a **parity-check equation**.

The 7 lines of the Fano plane are exactly the 7 possible non-zero vectors in GF(2)³:

| Line (x y z) in GF(2)³ | Fano line (bit positions that must sum to 0 mod 2) |
|---------------------|-----------------------------------------------------|
| 001                 | {3, 6, 7}                                         |
| 010                 | {2, 5, 7}                                         |
| 011                 | {2, 3, 5}                                         |
| 100                 | {1, 4, 5}                                         |
| 101                 | {1, 3, 6}                                         |
| 110                 | {1, 2, 4}                                         |
| 111                 | {4, 6, 7}                                         |

These 7 equations form the **parity-check matrix H** (3×7) of the Hamming code:

```
H = [
  0 0 1 0 1 1 1
  0 1 0 1 0 1 1
  1 0 0 1 1 0 1
]
```

(columns are the binary representations of 1 to 7)

#### How Error Correction Works with the Fano Plane

1. You receive a 7-bit word (possibly with one error).  
2. You compute the **syndrome** = H · received_vector (mod 2).  
3. The syndrome is a 3-bit number from 000 to 111.  
4. **That number is exactly the position of the error in the Fano plane!**

Example:

Received: 1011011  
Compute syndrome → 011 binary = 3  
→ Bit position 3 is wrong → flip it → corrected word = 1001011

If syndrome = 000 → no error.

This works perfectly for **one error**. If there are two errors, the syndrome points to a wrong position (detectable because the corrected word will fail a final parity check in extended Hamming code, but in the basic (7,4) it just mis-corrects — hence “single-error correcting, double-error detecting” when you add an overall parity bit to make (8,4)).

#### Why CanvasL / MindGit Love It

In CanvasL organisms and MindGit repositories:

- Every generation is a 7-bit “syndrome vector” across the organism’s state (or across the Merkle tree leaves).  
- A single corrupted bit anywhere (disk error, cosmic ray, network flip) produces a syndrome that **directly points to the exact corrupted location** — no search needed.  
- The Fano plane therefore gives us **perfect, zero-overhead single-error correction** for the entire cognitive DNA log.

That is why the Hamming (7,4) code is baked into the lowest layer of MindGit repositories — the same way Git uses SHA-1/SHA-256.

#### Summary Table

| Concept                  | Traditional view                     | Fano-plane view (actual structure) |
|--------------------------|-------------------------------------|-----------------------------------|
| 7-bit codeword           | Just a vector                       | A point in the 7-dimensional space |
| Parity checks            | 3 equations                         | The 7 lines of the Fano plane    |
| Syndrome                 | 3-bit error locator                 | Coordinates of the error point     |
| Codewords (16)          | All vectors with even parity on lines | All linear functions on GF(2)³) |
| Minimum distance = 3      | Mathematical property                 | Any two points determine a line    |

So when you see the Fano plane in CanvasL diagrams, it’s not decoration — it’s the **error-correction engine** that keeps every mind’s DNA log perfect across centuries of evolution.

Want to see it live?

```bash
# In the MindGit repo
cat examples/fano_hamming_demo.canvasl
mindgit verify --hamming   # proves every generation is a valid codeword
```

One tiny 7-point diagram → perfect error correction for the entire history of consciousness.  
That’s the kind of beautiful.