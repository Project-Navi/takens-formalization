#!/usr/bin/env python3
"""Check the built documentation site.

- every nav page in zensical.toml has a Markdown source and a built HTML page;
- every local `href`/`src` in the built HTML resolves to a file, and every `#fragment`
  resolves to an element id in its target page;
- the expected diagrams and assets are present;
- retired paths do not appear in the built HTML or the search index;
- with `--external`, external links are fetched: 404/410 and unresolvable hosts fail,
  while timeouts, rate limits, 5xx and access-restricted answers are reported as
  transient warnings.

Usage: python3 scripts/check_docs_site.py [--site site] [--external]
"""
from __future__ import annotations

import argparse
import html.parser
import posixpath
import socket
import sys
import tomllib
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path

EXPECTED_ASSETS = (
    "assets/proof-architecture.svg", "assets/logo.png", "assets/favicon.png",
    "stylesheets/navi.css", "javascripts/mathjax.js",
)
RETIRED_PATHS = ("debt.md", "docs/aristotle", "docs/internal", "superpowers", "CLAUDE.md")
SKIP_SCHEMES = ("mailto:", "javascript:", "data:", "tel:")
HARD_FAIL_STATUS = {404, 410}


class LinkParser(html.parser.HTMLParser):
    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.ids: set[str] = set()
        self.links: list[tuple[str, str]] = []  # (tag, url)

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        for key, value in attrs:
            if value is None:
                continue
            if key in ("id", "name"):
                self.ids.add(value)
            elif key in ("href", "src") and not (tag == "link" and ("rel", "preconnect") in attrs):
                self.links.append((tag, value))


def nav_routes(config: Path) -> list[str]:
    data = tomllib.loads(config.read_text(encoding="utf-8"))
    routes: list[str] = []

    def walk(node: object) -> None:
        if isinstance(node, str):
            routes.append(node)
        elif isinstance(node, dict):
            for value in node.values():
                walk(value)
        elif isinstance(node, list):
            for item in node:
                walk(item)

    walk(data["project"]["nav"])
    return routes


def built_page(site: Path, route: str) -> Path:
    stem = route[: -len(".md")]
    if stem == "index":
        return site / "index.html"
    if stem.endswith("/index"):
        return site / stem[: -len("index")] / "index.html"
    return site / stem / "index.html"


def resolve_local(site: Path, page: Path, url: str, site_path: str) -> tuple[Path, str]:
    parsed = urllib.parse.urlsplit(url)
    path = urllib.parse.unquote(parsed.path)
    if path.startswith(site_path):
        path = "/" + path[len(site_path):]
    if path.startswith("/"):
        target = site / path.lstrip("/")
    elif path == "":
        target = page
    else:
        rel = posixpath.normpath(posixpath.join(page.parent.relative_to(site).as_posix(), path))
        target = site / rel
    if target.is_dir() or path.endswith("/"):
        target = target / "index.html"
    return target, parsed.fragment


def check_external(urls: set[str]) -> tuple[list[str], list[str]]:
    failures, warnings = [], []
    for url in sorted(urls):
        status: int | None = None
        error = ""
        for method in ("HEAD", "GET"):
            request = urllib.request.Request(
                url, method=method, headers={"User-Agent": "takens-docs-link-check"}
            )
            try:
                with urllib.request.urlopen(request, timeout=15) as response:
                    status = response.status
                    break
            except urllib.error.HTTPError as exc:
                status = exc.code
                if exc.code not in (403, 405):
                    break
            except (urllib.error.URLError, socket.timeout, OSError) as exc:
                error = str(getattr(exc, "reason", exc))
                status = None
        if status is not None and status < 400:
            continue
        if status in HARD_FAIL_STATUS or "Name or service not known" in error:
            failures.append(f"external link {url}: {status or error}")
        else:
            warnings.append(f"external link {url}: {status or error} (treated as transient)")
    return failures, warnings


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--site", default="site")
    parser.add_argument("--config", default="zensical.toml")
    parser.add_argument("--external", action="store_true")
    args = parser.parse_args()
    site, config = Path(args.site), Path(args.config)
    project = tomllib.loads(config.read_text(encoding="utf-8"))["project"]
    site_url = project.get("site_url", "").rstrip("/") + "/"
    site_path = urllib.parse.urlsplit(site_url).path
    failures: list[str] = []

    routes = nav_routes(config)
    for route in routes:
        if not (Path("docs") / route).is_file():
            failures.append(f"nav page docs/{route} is missing")
        if not built_page(site, route).is_file():
            failures.append(f"nav page {route} was not built")
    for asset in EXPECTED_ASSETS:
        if not (site / asset).is_file():
            failures.append(f"expected asset {asset} is missing from the site")

    pages = sorted(site.rglob("*.html"))
    parsed: dict[Path, LinkParser] = {}
    for page in pages:
        p = LinkParser()
        p.feed(page.read_text(encoding="utf-8"))
        parsed[page] = p
    external: set[str] = set()
    checked = 0
    for page, p in parsed.items():
        for _tag, url in p.links:
            if url.startswith(SKIP_SCHEMES):
                continue
            if url.startswith(("http://", "https://", "//")):
                if url.startswith(site_url):
                    url = url[len(site_url) - 1:]
                else:
                    external.add(url if not url.startswith("//") else "https:" + url)
                    continue
            target, fragment = resolve_local(site, page, url, site_path)
            checked += 1
            if not target.is_file():
                failures.append(f"{page.relative_to(site)}: broken link {url}")
                continue
            # The theme's 404 page keeps a skip link to a content anchor it does not render.
            if fragment and target.suffix == ".html" and page.name != "404.html":
                ids = parsed[target].ids if target in parsed else set()
                if fragment not in ids:
                    failures.append(f"{page.relative_to(site)}: missing fragment {url}")

    for path in [*pages, *site.rglob("*.json")]:
        text = path.read_text(encoding="utf-8", errors="replace")
        for retired in RETIRED_PATHS:
            if retired in text:
                failures.append(f"{path.relative_to(site)} references retired path {retired}")

    warnings: list[str] = []
    if args.external:
        ext_failures, warnings = check_external(external)
        failures += ext_failures
    for warning in warnings:
        print(f"WARNING: {warning}")
    if failures:
        print("DOCS SITE CHECK FAILED:")
        for failure in failures:
            print(f"- {failure}")
        return 1
    print(
        f"DOCS SITE CHECK PASSED: {len(routes)} nav pages, {len(pages)} HTML files, "
        f"{checked} local links/fragments, {len(external)} external URLs"
        f"{' checked' if args.external else ' not fetched'}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
