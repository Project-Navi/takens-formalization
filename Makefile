.PHONY: docs-serve docs-build

docs-serve:
	uv run zensical serve

docs-build:
	uv run zensical build
