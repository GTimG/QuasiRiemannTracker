# The quartic QRH boundary

Hailey Collet · HaileyCollet@gmail.com · Apache-2.0

The rendered manuscript has 58 A4 pages. `paper.tex` is standalone and can be
compiled with XeLaTeX or Tectonic; the supplied PDF was compiled with Tectonic
0.17.0. For example, from this directory:

```sh
tectonic --untrusted paper.tex
```

The first build may download standard TeX packages and fonts. After those are
cached, `tectonic --only-cached --untrusted paper.tex` compiles offline. PDF
metadata such as creation time can change the PDF bytes when rebuilding.
The mathematical Markdown source is `paper.md`; the TeX adds the title,
abstract and equation line wrapping for print. All 18 display-formatting
transformations preserve the mathematical tokens, apart from equivalent
explicit multiplication and delimiter sizing. The rendered pages were
visually checked, with no overfull boxes or missing-character warnings.

The PDF is published at `public/proofs/cycle25-quartic-20261010/paper.pdf`
in the tracker repository and on the author's research page. It is kept
outside the UTF-8-only source archive. `paper-files.json` records the exact
published manuscript hashes. See `../PROVENANCE.md` for authorship and reuse.
