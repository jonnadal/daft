.PHONY: all clean compile docs

all: docs

clean:
	rm -rf docs/

docs: docs/ExBackup.html docs/Seqs.html
docs/%.html: %.dfy docco-languages.json
	docco --languages docco-languages.json $<

verify:
	Dafny /ironDafny /compile:0 $(shell find . -name '*.dfy' -not -name 'flycheck_*')
