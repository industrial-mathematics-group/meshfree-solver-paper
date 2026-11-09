# Journal of Scientific Computing submission version

`main_jsc.tex` is the version of `../paper/main_light.tex` formatted for the Journal of Scientific Computing (Springer). `../paper/` stays unchanged: it is the preprint archived at https://zenodo.org/records/23807966.

Build: `latexmk -pdf main_jsc.tex`. The folder is self-contained. It holds the figures (copies of `../paper/figures/`), `refs.bib`, and the class and style files from Springer's official author package `LaTeX_DL_468198_240419` (`svjour3.cls` v3.2, `svglov3.clo`, `spmpsci.bst`), so it can be uploaded as it is.

**Layout.** The journal asks for `svjour3` with the option `smallextended`, which sets a 119 mm × 195 mm text block for the journal's page format but prints it at the top left of an A4 sheet. `main_jsc.tex` therefore sets the PDF page to the trim size of published JSC articles, 155 mm × 235 mm, with the text block centred. Delete the marked lines after `\smartqed` to get the class's A4 output; the line and page breaks stay the same. The two-dimensional colour maps are scaled to 72–74 % of the text width so that text fits on their pages, which keeps the figures within the text.

Placeholders are printed in red as `[TODO: …]`:
- the corresponding author and their e-mail, and the ORCIDs (title page)
- the competing-interests statement and the author contribution statement (Declarations)
- the Zenodo DOI of the archive of this repository (Data and Code availability; `JungAddendum2026` in `refs.bib`)

Changes against `../paper/` are the class and title page, the abstract (246 words, no undefined abbreviations), six keywords, the MSC codes, the Declarations section before the references, the reference style (`spmpsci`, full DOI links, abbreviated journal names), Springer caption style, and widths fitted to the narrower text block.
