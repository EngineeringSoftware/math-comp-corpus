# MathComp Corpus

A corpus of code for the [Coq proof assistant](https://coq.inria.fr) along with several
independently machine-readable representations, derived from verification
projects related to the [Mathematical Components][math-comp-website] (MathComp) library.
The corpus can be used, e.g., in machine learning and data mining applications.
Machine-readable representations are in the form of [S-expressions][sexp-link] (sexps),
and were created using the [SerAPI library][serapi-website].

[math-comp-website]: https://math-comp.github.io
[serapi-website]: https://github.com/ejgallego/coq-serapi
[sexp-link]: https://en.wikipedia.org/wiki/S-expression

## Obtaining the corpus

The latest released version of the corpus can be [downloaded][download-link]
from GitHub. The archive includes both the Coq source files and corresponding
machine-readable representations.

[download-link]: https://github.com/EngineeringSoftware/math-comp-corpus/releases

## Corpus contents

The latest corpus release is based on [Coq 8.10.2][coq-8102] and [MathComp 1.9.0][mathcomp-190],
and contains 449 source files from 21 Coq projects --- in total over 297k lines of code (LOC).
For each source file (e.g., `theory.v`), there are two corresponding files with lists of
sexps, organized at the Coq sentence level, for tokens (`theory.tok.sexp`)
and abstract syntax trees (`theory.ast.sexp`). Moreover, three sexp representations
are provided for each Coq lemma statement in the corpus: tokens, abstract syntax tree, and
elaborated term. All machine-readable representations were created using [SerAPI 0.7.1][serapi-071],
via the SerAPI-bundled programs `sercomp`, `sertok`, and `sername`.

A [research paper][arxiv-paper] describes the corpus in more detail
and provides additional statistics. The corpus is divided into three tiers based
on how well projects conform to the [MathComp conventions][math-comp-contrib].

| Project                            | Revision SHA | No. files  | LOC    | Tier | License                  |
|:---------------------------------- |:------------:|-----------:|-------:|-----:|:-------------------------|
| [finmap][finmap]                   | 27642a8      | 4          | 6451   | 1    | [CECILL-B][cecill-b]     |
| [fourcolor][fourcolor]             | 0851d49      | 60         | 37138  | 1    | [CECILL-B][cecill-b]     |
| [math-comp][math-comp]             | 748d716      | 89         | 84713  | 1    | [CECILL-B][cecill-b]     |
| [odd-order][odd-order]             | ca602a4      | 34         | 36125  | 1    | [CECILL-B][cecill-b]     |
| [analysis][analysis]               | 9e5fe1d      | 17         | 11739  | 2    | [CECILL-C][cecill-c]     |
| [bigenough][bigenough]             | 5f79a32      | 1          | 78     | 2    | [CECILL-B][cecill-b]     |
| [elliptic-curves][elliptic-curves] | 631af89      | 18         | 9596   | 2    | [CECILL-B][cecill-b]     |
| [grobner][grobner]                 | dfa54f9      | 1          | 1330   | 2    | [CECILL-B][cecill-b]     |
| [infotheo][infotheo]               | 6c17242      | 81         | 42295  | 2    | [GPL-3.0-only][gpl3]     |
| [multinomials][multinomials]       | 691d795      | 5          | 7363   | 2    | [CECILL-B][cecill-b]     |
| [real-closed][real-closed]         | 495a1fa      | 10         | 8925   | 2    | [CECILL-B][cecill-b]     |
| [robot][robot]                     | b341ad1      | 13         | 11130  | 2    | [LGPL-3.0-only][lgpl3]   |
| [two-square][two-square]           | 1c09aca      | 2          | 1721   | 2    | [CECILL-B][cecill-b]     |
| [bits][bits]                       | 3cd298a      | 10         | 4041   | 3    | [Apache-2.0][apache2]    |
| [comp-dec-pdl][comp-dec-pdl]       | c1f813b      | 16         | 4419   | 3    | [CECILL-B][cecill-b]     |
| [disel][disel]                     | e8aa80c      | 20         | 4473   | 3    | [BSD-2-Clause][bsd2]     |
| [fcsl-pcm][fcsl-pcm]               | eef4503      | 12         | 5789   | 3    | [Apache-2.0][apache2]    |
| [games][games]                     | 3d3bd31      | 12         | 4953   | 3    | [BSD-2-Clause][bsd2]     |
| [monae][monae]                     | 9d0e461      | 18         | 6655   | 3    | [GPL-3.0-only][gpl3]     |
| [reglang][reglang]                 | da333e0      | 12         | 3033   | 3    | [CECILL-B][cecill-b]     |
| [toychain][toychain]               | 97bd697      | 14         | 5275   | 3    | [BSD-2-Clause][bsd2]     |

The structure of the corpus is as follows:

| File/directory                 | Contents                                                                               |
|:-------------------------------|:---------------------------------------------------------------------------------------|
| `projects.yml`                 | List of projects, along with their URL, SHA, build command, installation command, etc. |
| `raw-files`                    | Project source files and their machine-readable representations.                       |
| `lemmas`                       | Lemmas for all projects in the corpus and their machine-readable statements.           |
| `lemmas-filtered`              | Subset of lemmas obeying restrictions on the maximum sizes of elaborated terms.        |
| `definitions`                  | Definitions extracted from the corpus.                                                 |

[finmap]: https://github.com/math-comp/finmap
[fourcolor]: https://github.com/math-comp/fourcolor
[math-comp]: https://github.com/math-comp/math-comp
[odd-order]: https://github.com/math-comp/odd-order
[analysis]: https://github.com/math-comp/analysis
[bigenough]: https://github.com/math-comp/bigenough
[elliptic-curves]: https://github.com/strub/elliptic-curves-ssr
[grobner]: https://github.com/thery/grobner
[multinomials]: https://github.com/math-comp/multinomials
[real-closed]: https://github.com/math-comp/real-closed
[robot]: https://github.com/affeldt-aist/coq-robot
[two-square]: https://github.com/thery/twoSquare
[bits]: https://github.com/coq-community/coq-bits
[comp-dec-pdl]: https://github.com/palmskog/comp-dec-pdl
[disel]: https://github.com/DistributedComponents/disel
[fcsl-pcm]: https://github.com/imdea-software/fcsl-pcm
[games]: https://github.com/gstew5/games
[monae]: https://github.com/palmskog/monae
[reglang]: https://github.com/palmskog/coq-reglang
[toychain]: https://github.com/certichain/toychain
[infotheo]: https://github.com/palmskog/infotheo

[cecill-b]: https://spdx.org/licenses/CECILL-B.html
[cecill-c]: https://spdx.org/licenses/CECILL-C.html
[lgpl3]: https://spdx.org/licenses/LGPL-3.0-only.html
[gpl3]: https://spdx.org/licenses/GPL-3.0-only.html
[apache2]: https://spdx.org/licenses/Apache-2.0.html
[bsd2]: https://spdx.org/licenses/BSD-2-Clause.html

[coq-8102]: https://github.com/coq/coq/releases/tag/V8.10.2
[mathcomp-190]: https://github.com/math-comp/math-comp/releases/tag/mathcomp-1.9.0
[serapi-071]: https://github.com/ejgallego/coq-serapi/releases/tag/8.10.0%2B0.7.1
[arxiv-paper]: https://arxiv.org/abs/2004.07761
[math-comp-contrib]: https://github.com/math-comp/math-comp/blob/mathcomp-1.9.0/CONTRIBUTING.md

## Applications

The corpus was used to train and evaluate the tool
[Roosterize][roosterize-website], which suggests lemma
names in Coq code using neural networks.

If you have used the corpus in a research project, please cite
the corresponding research paper in any related publication:
```bibtex
@inproceedings{NieETAL20Roosterize,
  author = {Nie, Pengyu and Palmskog, Karl and Li, Junyi Jessy and Gligoric, Milos},
  title = {Deep Generation of {Coq} Lemma Names Using Elaborated Terms},
  booktitle = {International Joint Conference on Automated Reasoning},
  pages = {97--118},
  doi = {10.1007/978-3-030-51054-1_6},
  year = {2020},
}
```

[roosterize-website]: https://github.com/EngineeringSoftware/roosterize

## Example data

The Coq lemma sentence
```coq
Lemma mg_eq_proof L1 L2 (N1 : mgClassifier L1) : L1 =i L2 -> nerode L2 N1.
```
is serialized into the following tokens (simplified):
```lisp
(Sentence((IDENT Lemma)(IDENT mg_eq_proof)(IDENT L1)(IDENT L2)
  (KEYWORD"(")(IDENT N1)(KEYWORD :)(IDENT mgClassifier)
  (IDENT L1)(KEYWORD")")(KEYWORD :)(IDENT L1)(KEYWORD =i)(IDENT L2)
  (KEYWORD ->)(IDENT nerode)(IDENT L2)(IDENT N1)(KEYWORD .)))
```
and the corresponding parsed syntax (simplified):
```lisp
(VernacExpr()(VernacStartTheoremProof Lemma (Id mg_eq_proof)
 (((CLocalAssum(Name(Id L1))(CHole()IntroAnonymous()))
   (CLocalAssum(Name(Id L2))(CHole()IntroAnonymous()))
   (CLocalAssum(Name(Id N1))
    (CApp(CRef(Ser_Qualid(DirPath())(Id mgClassifier)))(CRef(Ser_Qualid(DirPath())(Id L1))))))
  (CNotation(InConstrEntrySomeLevel"_ -> _")
   (CNotation(InConstrEntrySomeLevel"_ =i _")
    (CRef(Ser_Qualid(DirPath())(Id L1)))(CRef(Ser_Qualid(DirPath())(Id L2))))
   (CApp(CRef(Ser_Qualid(DirPath())(Id nerode)))
    (CRef(Ser_Qualid(DirPath())(Id L2)))(CRef(Ser_Qualid(DirPath())(Id N1))))))))
```
and finally, the corresponding elaborated term (simplified):
```lisp
(Prod (Name (Id char)) ... (Prod (Name (Id L1)) ...
 (Prod (Name (Id L2)) ... (Prod (Name (Id N1)) ...
  (Prod Anonymous (App (Ref (DirPath ((Id ssrbool) (Id ssr) (Id Coq))) (Id eq_mem)) ...
   (Var (Id L1)) ... (Var (Id L2)))
  (App (Ref (DirPath ((Id myhill_nerode) (Id RegLang))) (Id nerode)) ...
   (Var (Id L2)) ... (Var (Id N1))))))))
```

## License

As described in more detail in the [license file](LICENSE), all corpus metadata is
licensed under the MIT license, while all Coq source files and corresponding
S-expression files are licensed under their respective original open-source licenses.

## Authors

- [Pengyu Nie](https://cozy.ece.utexas.edu/~pynie/)
- [Karl Palmskog](https://setoid.com)
- [Emilio Jesús Gallego Arias](https://www.irif.fr/~gallego/)
- [Junyi Jessy Li](http://jessyli.com)
- [Milos Gligoric](http://users.ece.utexas.edu/~gligoric/)
