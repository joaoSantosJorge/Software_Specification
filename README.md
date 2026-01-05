# Software Specification – Dafny Project

**Academic Year:** QS 2021/2022

> *“I don’t understand you,” said Alice. “It’s dreadfully confusing!”*
> *“That’s the effect of living backwards,” the Queen said kindly…*

— *Lewis Carroll, Through the Looking-Glass*

---

## Overview

This project focuses on reasoning about **reversal operations** across multiple data structures using **Dafny**. The exercises combine implementation and formal verification, emphasizing recursive definitions, invariants, and proofs of correctness.

---

## Exercise 1: Reversing Sequences (1 val)

1. Implement a recursive Dafny function `revSeq` that reverses a sequence of integers.

   ```
   revSeq([1, 2, 3]) == [3, 2, 1]
   ```

2. Prove that `revSeq` is its own inverse:

   ```
   revSeq(revSeq(s)) == s
   ```

3. Prove the distributivity property:

   ```
   revSeq(s1 + s2) == revSeq(s2) + revSeq(s1)
   ```

---

## Exercise 2: Reversing Arrays (1.5 val)

### 1. `reverseArr1`

Implement a method that returns a **new array** containing the reverse of the input array.

```dafny
method reverseArr1(arr: array<int>) returns (r: array<int>)
  ensures r[..] = revSeq(arr[..])
```

### 2. `reverseArr2`

Implement a method that **reverses an array in place**, without allocating a new array or sequence.

```dafny
method reverseArr2(arr: array<int>)
  ensures arr[..] = revSeq(old(arr[..]))
  modifies arr
```

> **Note:** To obtain full marks, at least one of the two methods must be implemented **iteratively**.

---

## Exercise 3: Reversing Binary Trees (1 val)

Given the inductive datatype:

```dafny
datatype Tree = Leaf(int) | Node(int, Tree, Tree)
```

1. Define a recursive function `revTree` that computes the **symmetric tree**.
2. Prove that `revTree` is its own inverse:

   ```
   revTree(revTree(t)) == t
   ```
3. Define a recursive function `sequentialise` that outputs a left-to-right sequence of all integers in the tree.
4. Prove the interchange property:

   ```
   sequentialise(revTree(t)) == revSeq(sequentialise(t))
   ```

> **Note:** At least one proof should be written in **calculational style**.

---

## Exercise 4: Reversing Object-Oriented Lists (1.5 val)

Consider the following partial implementation of a list node class:

```dafny
class LNode {
  ghost var list : seq<int>;
  ghost var footprint : set<Node>;

  var data : int;
  var next : LNode?;

  function Valid(): bool
    reads this, footprint
    decreases footprint
  {
    (this in footprint) ∧
    ((next == null) ==> list == [data] ∧ footprint == {this}) ∧
    ((next != null) ==>
      next in footprint ∧
      footprint == next.footprint + {this} ∧
      this !in next.footprint ∧
      list == [data] + next.list ∧
      next.Valid())
  }
}
```

### 1. `reverse1`

Return the head of a **new list** with reversed contents.

```dafny
method reverse1() returns (r: Node)
  requires Valid()
  ensures Valid() ∧ r.Valid() ∧ fresh(r.footprint)
  ensures r.list = revSeq(old(list))
```

### 2. `reverse2`

Reverse the list **in place**.

```dafny
method reverse2() returns (r: Node)
  requires Valid()
  ensures r.Valid() ∧ r.list = revSeq(old(list))
  ensures r.footprint = old(footprint)
  modifies footprint
```

---

## Submission Instructions

* The solution must consist of **four Dafny files**, one per exercise.
* Each exercise must be implemented in its **own Dafny module**.
* Exercises 2–4 may reuse definitions from Exercise 1 using `include` and `import`.
* Submit a **ZIP file** containing the four solution files via **Fenix**.
* **Deadline:** 22 October 2021, 23:59.

---

## Project Discussion

After submission, students may be asked to present their work and perform small modifications to verify understanding and originality.

---

## Academic Integrity

Submission implies a commitment of honour. Any form of plagiarism or unauthorized collaboration will result in **immediate failure** of the course for all involved parties.

---

## References

* Dafny Modules Tutorial: [https://dafny-lang.github.io/dafny/OnlineTutorial/Modules](https://dafny-lang.github.io/dafny/OnlineTutorial/Modules)
