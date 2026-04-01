This project is part of my preparation for research in programming languages, particularly in type systems and formal methods.

# Bidirectional Typing Formalization in Lean 4

This repository provides a formalization of **Bidirectional Type Systems**, bridging the gap between theoretical specifications and deterministic type-checking algorithms.

## 🎯 Purpose

- **Mechanization**: To implement a sound and deterministic bidirectional type-checking algorithm in Lean 4.
- **Verification**: To prove **Soundness** (the algorithm follows the rules) and **Uniqueness** (synthesis results are deterministic).
- **Research**: To explore the design principles of bidirectional typing as discussed in modern PL research (e.g., Dunfield & Krishnaswami, 2020) and TaPL.
- **Extensibility**: To build a foundation for formalizing more advanced type systems (e.g., Subtyping, System F, and Dependent Types).

## 📚 Scope

This project currently mechanizes a Simply Typed Lambda Calculus (STLC) augmented with type annotations:
- **Checking Mode ($\Leftarrow$)**: Handles unit and lambda abstractions (introduction rules).
- **Synthesis Mode ($\Rightarrow$)**: Handles variables, applications, and annotations (elimination rules).
- **Direction Change**: Automatic subsumption from synthesis to checking.

### Future Roadmap
- [ ] **Subtyping ($A <: B$)**: Integration of subtyping rules into the bidirectional framework (TaPL Chapter 15).
- [ ] **Polymorphism (System F)**: Handling universal quantifiers and type abstraction.
- [ ] **Advanced Features**: Recursive types, Linear types, and Effect systems.

## 🔬 Research Context & Design Principles

This formalization is informed by the **"Pfenning Recipe"** and criteria from:
- **Jana Dunfield and Neel Krishnaswami (2020)**: *Bidirectional Typing*. [arXiv:1908.05839](https://arxiv.org/abs/1908.05839).
- **Benjamin C. Pierce (2002)**: *Types and Programming Languages* (TaPL).

### Core Principles
- **Mode Correctness**: Ensuring inputs and outputs are logically consistent within each typing judgment.
- **Completeness**: Guaranteeing that every derivable typing in the original system can be checked by the bidirectional system (with appropriate annotations).
- **Pfenning Recipe**: Introduction rules are handled in Checking mode, while Elimination rules are handled in Synthesis mode.


## 🧠 Technical Highlights (Lean 4)

- **Termination via Lexicographic Order**: We prove the algorithm terminates using a lexicographic measure $(sizeOf(e), mode)$ where $Synth=0$ and $Check=1$.
- **Curry-Howard Isomorphism**: Implementation of uniqueness as a structural recursive function (`match` statement) that doubles as a mathematical proof.
- **TaPL Chapter 2 Foundations**: Rigorous use of relations, orders, and inductive definitions as established in the mathematical preliminaries of TaPL.

## 📄 License

This project is licensed under the **MIT License**. See the [LICENSE](LICENSE) file for details.

## ⚠️ AI Training and Usage Restriction

The contents of this repository, including source code, documentation, and associated materials, are provided for educational and research purposes. **Use of this repository for training machine learning models, including but not limited to large language models (LLMs), is strictly prohibited** without explicit prior written consent from the author.

This includes, but is not limited to:
- Dataset creation for machine learning.
- Pretraining or fine-tuning of AI models.
- Embedding or indexing for retrieval-based systems.

## ⚙️ Environment Setup

### Installing Lean
Please follow the [official installation guide](https://lean-lang.org/lean4/doc/setup.html).

### Setup
After installing Lean, run the following command to download dependencies:
```bash
lake update && lake exe cache get
