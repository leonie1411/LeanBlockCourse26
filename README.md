# Formalizing Verification in Lean – FUB Block Course 2026

## Announcements

*There are currently no Announcements.*

## About us

[Christoph Spiegel](https://christophspiegel.berlin) will teach this course. He is a researcher at ZIB in Prof. Pokutta’s IOL group, working on combinatorics, optimization, machine learning, and proof formalization. [Silas Rathke](https://www.mi.fu-berlin.de/en/math/groups/geokomb/People/PhD-Students/Silas_Rathke.html) will serve as the teaching assistant. He is a Ph.D. student at FUB in Prof. Szabo’s group, focusing on extremal combinatorics and related formalization projects.

## General notes

* This is the second time this course is being held. The structure will largely follow last year's with some additions and modifications, but is nevertheless subject to (spontaneous) change. Constructive feedback is welcomed throughout the course and afterwards.
* The course is split into two sessions (9:30 to 12:30 and 14:00 to 17:00) each day and takes place from **Monday the 2nd of March** to **Friday the 13th of March 2026**. The venue has not yet been settled, but the course will be helf on the Dahlem Campus, either at FUB or ZIB.
* The course is open to everyone, including guest auditors (Gasthörer), not just those who need it for their degree. However, priority will be given to FU students who need the course as part of their ABV degree program. The course will also be offered for **Master students at the FUB** as well as as a **BMS Advanced Course** for the first time this year! For the `aktive Teilnahme', Master-level participants will be required to solve additional and more advanced problems in the exercise sessions compared to Bachelor-level students. Both Bachelor and Master-level students will be given the same **final exam on the second Friday at the end of the course**. There will be an **additional final project task for the Master-level students** that the students will be given one or two weeks time after the end of the block course to solve. The exact scope of that additional project and the format of the evaluation of it has not yet been determined but may include an in-person presentation.
* Participants **need to bring a laptop** to do the exercises and follow along during the course and work on exercises and project work.
* Completion of Analysis I and Linear Algebra I should provide a sufficient mathematical background, but participants should have a strong understanding of these subjects, as formal proof verification is very "unforgiving". No prior programming experience is required, but a certain "technical affinity and interest" is needed. Besides formal proof verification, you will be in contact with many other tools such as `git` and `github`, [Patrick Massot's](https://www.imo.universite-paris-saclay.fr/~patrick.massot/en/) `leanblueprint`, containerization through `docker`, CI/CD in the form of `github Actions`, as well as various ML tools.
* The course will be **conducted in English**, but Bachelor students taking the course as part of their ABV requirements may express themselves in German if they prefer.

## Technical difficulties

### `git` and `github`

*No information yet.*

### Wrangling `lean` and `lake`

* `lake init ProjectName math` sets up a project with mathlib as a dependency in the current folder.
* `lake build` builds the project.
* If your info view shows that it is compiling a lot of files from mathlib, then (1) run `pkill -f lean` (MacOS / Linux) or `Stop-Process -Name *lean* -Force` (Windows) to kill the running Lean processes, (2) remove the `.lake` folder, e.g., by running `rm -rf .lake` in a POSIX complaint OS, and run `lake clean`, (3) run `lake exe cache get` to download the mathlib binaries again, and finally (4) restart the Lean server by clicking on the `∀` button in VS Code and choosing `Server: Restart Server`.

### `leanblueprint`

*No information yet.*

### Containerization with `docker` and CI/CD through `git Actions`

*No information yet.*

### `claude`, `codex`, and other LLM tools

*No information yet.*

## Resources

### Documentation and search
* The [mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/index.html) is the official documentation of the [mathlib library](https://github.com/leanprover-community/mathlib4)
* [LeanSearch](https://leansearch.net) is a helpful resource for finding results in mathlib

### Text books
* [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/) by Jeremy Avigad, Leonardo de Moura, Soonho Kong, Sebastian Ullrich
* [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) by Jeremy Avigad and Patrick Massot
* [The Hitchhiker’s Guide to Logical Verification](https://cs.brown.edu/courses/cs1951x/static_files/main.pdf) by Anne Baanen, Alexander Bentkamp, Jasmin Blanchette, Johannes Hölzl, Jannis Limperg
* [The Mechanics of Proof](https://hrmacbeth.github.io/math2001/) by Heather Macbeth
* [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/) by David Thrane Christiansen

### Talks

* Kevin Buzzard's talk on [The rise of formalism in mathematics](https://www.youtube.com/watch?v=SEID4XYFN7o) at ICM22

### A more playful approach
* The [Lean Game Server](https://adam.math.hhu.de) inspired many of the smaller exercises
