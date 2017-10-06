all: \
	homod/homod.pdf \
	homod/homod.maude \
	homod/homod.hs

%.pdf: %.md
	pandoc --filter pandoc-citeproc --from markdown --to latex --output $@ $<

homod/homod.maude: homod/homod.md
	pandoc-tangle --from markdown --to code-maude --code maude $< > $@

homod/homod.hs: homod/homod.md
	pandoc-tangle --from markdown --to code-haskell --code haskell $< > $@
