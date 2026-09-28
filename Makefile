.PHONY: build lint verify audit test-checkers docs-build docs-check docs-serve

build:
	lake build --wfail $$(python3 scripts/check_source.py --list-modules)

lint:
	lake lint

audit:
	python3 scripts/check_source.py

verify:
	python3 scripts/check_axioms.py
	python3 scripts/check_doc_names.py
	lake env leanchecker --fresh TakensFormal

test-checkers:
	python3 scripts/test_checkers.py --lean

docs-build:
	uv run zensical build --clean

docs-check: docs-build
	python3 scripts/check_docs_site.py

docs-serve:
	uv run zensical serve
