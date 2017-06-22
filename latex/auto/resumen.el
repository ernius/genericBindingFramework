(TeX-add-style-hook
 "resumen"
 (lambda ()
   (TeX-run-style-hooks
    "latex2e"
    "beamer"
    "beamer10"
    "graphicx"
    "agda"
    "amsmath"
    "amssymb"
    "stmaryrd"
    "mathtools"
    "textgreek"
    "catchfilebetweentags"
    "tipa"
    "newunicodechar")
   (TeX-add-symbols
    '("Wider" ["argument"] 1))
   (LaTeX-add-labels
    "sec:fold"
    "sec:pimind")
   (LaTeX-add-bibliographies
    "resumen.bib"))
 :latex)

