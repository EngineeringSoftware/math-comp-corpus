# MathComp Corpus

A corpus of code for the [Coq proof assistant](https://coq.inria.fr) along with several
machine-readable representations, derived from verification
projects related to the [Mathematical Components][mathcomp-website] (MathComp) library.
The corpus can be used, e.g., in machine learning and data mining applications.
Machine-readable representations were created using the [SerAPI library][serapi-website].

[mathcomp-website]: https://math-comp.github.io
[serapi-website]: https://github.com/ejgallego/coq-serapi

<b>We are actively updating this repository and will make it ready by
the end of May. Stay tuned!</b>

## Obtaining the corpus

The latest released version of the corpus can be [downloaded][download-link]
from GitHub. The archive includes both the source files written in Coq and files containing
machine-readable representations; the latter were created using [Coq 8.10.2][coq-8102]
and [SerAPI 0.7.1][serapi-071], via the SerAPI programs `sercomp`, `sertok`, and `sername`.

[download-link]: https://github.com/EngineeringSoftware/mathcomp-corpus/releases
[coq-8102]: https://github.com/coq/coq/releases/tag/V8.10.2
[serapi-071]: https://github.com/ejgallego/coq-serapi/releases

## Corpus contents

The latest release of the corpus, based on MathComp 1.9.0, consists of 449 source files
from 21 Coq projects --- in total over 297k lines of code (LOC).

| Project                            | Revision SHA | No. files  | LOC    |
|:---------------------------------- |:------------:|-----------:|-------:|
| [finmap][finmap]                   | 27642a8      | 4          | 6451   |
| [fourcolor][fourcolor]             | 0851d49      | 60         | 37138  |
| [math-comp][math-comp]             | 748d716      | 89         | 84713  |
| [odd-order][odd-order]             | ca602a4      | 34         | 36125  |
| [analysis][analysis]               | 9e5fe1d      | 17         | 11739  |
| [bigenough][bigenough]             | 5f79a32      | 1          | 78     |
| [elliptic-curves][elliptic-curves] | 631af89      | 18         | 9596   |
| [grobner][grobner]                 | dfa54f9      | 1          | 1330   |
| [multinomials][multinomials]       | 691d795      | 5          | 7363   |
| [real-closed][real-closed]         | 495a1fa      | 10         | 8925   |
| [robot][robot]                     | b341ad1      | 13         | 11130  |
| [two-square][two-square]           | 1c09aca      | 2          | 1721   |
| [bits][bits]                       | 3cd298a      | 10         | 4041   |
| [comp-dec-pdl][comp-dec-pdl]       | c1f813b      | 16         | 4419   |
| [disel][disel]                     | e8aa80c      | 20         | 4473   |
| [fcsl-pcm][fcsl-pcm]               | eef4503      | 12         | 5789   |
| [games][games]                     | 3d3bd31      | 12         | 4953   |
| [monae][monae]                     | 9d0e461      | 18         | 6655   |
| [reglang][reglang]                 | da333e0      | 12         | 3033   |
| [toychain][toychain]               | 97bd697      | 14         | 5275   |
| [infotheo][infotheo]               | 6c17242      | 81         | 42295  |

A [research paper][arxiv-paper] describes the corpus in more detail
and provides additional statistics.

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

[arxiv-paper]: https://arxiv.org/abs/2004.07761

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
  pages = {To appear},
  year = {2020},
}
```

[roosterize-website]: https://github.com/EngineeringSoftware/roosterize

## Example data

The Coq lemma sentence
```coq
Lemma mg_eq_proof L1 L2 (N1 : mgClassifier L1) : L1 =i L2 -> nerode L2 N1.
```
is serialized into the following tokens:
```lisp
(Sentence((IDENT Lemma)(IDENT mg_eq_proof)(IDENT L1)(IDENT L2)
  (KEYWORD"(")(IDENT N1)(KEYWORD :)(IDENT mgClassifier)
  (IDENT L1)(KEYWORD")")(KEYWORD :)(IDENT L1)(KEYWORD =i)(IDENT L2)
  (KEYWORD ->)(IDENT nerode)(IDENT L2)(IDENT N1)(KEYWORD .)))
```
and the corresponding parsed syntax:
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
and finally, the corresponding elaborated term:
```lisp
(Prod (Name (Id char)) ... (Prod (Name (Id L1)) ...
 (Prod (Name (Id L2)) ... (Prod (Name (Id N1)) ...
  (Prod Anonymous (App (Ref (DirPath ((Id ssrbool) (Id ssr) (Id Coq))) (Id eq_mem)) ...
   (Var (Id L1)) ... (Var (Id L2)))
  (App (Ref (DirPath ((Id myhill_nerode) (Id RegLang))) (Id nerode)) ...
   (Var (Id L2)) ... (Var (Id N1))))))))
```

## Authors

- [Pengyu Nie](https://cozy.ece.utexas.edu/~pynie/)
- [Karl Palmskog](https://setoid.com)
- [Emilio Jesús Gallego Arias](https://www.irif.fr/~gallego/)
- [Junyi Jessy Li](http://jessyli.com)
- [Milos Gligoric](http://users.ece.utexas.edu/~gligoric/)
