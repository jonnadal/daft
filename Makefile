.PHONY: all clean docs verify

all: docs verify

clean:
	rm -rf docs/

docs: docs/dfy/ExBackup.html docs/dfy/Seqs.html docs/js/minimal-sat.html
docs/js/%.html: %.js
	docco --output docs/js/ $<
docs/dfy/%.html: %.dfy docco-languages.json
	docco --languages docco-languages.json --output docs/dfy/ $<

verify:
	Dafny /ironDafny /compile:0 $(shell find . -name '*.dfy' -not -name 'flycheck_*')
	npm install
	PROJ=minimal-sat npm test
