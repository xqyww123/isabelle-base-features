# fast_abbrev_printing

When Isabelle2025-2 prints a term, it turns every expansion of an abbreviation back into the
abbreviation. Inside a locale with many constants defined in it or in the locales it imports, as in
many AFP entries, this step takes almost all of the printing time. This feature makes that step 3
to 35 times faster in the contexts measured; the printed text stays the same, byte for byte.

You may want it if showing goals, facts or search results is slow inside such a locale and becomes
fast with `declare [[show_abbrevs = false]]`.

Other feature packages build on this one, so it may have come in as a dependency.
[`details.md`](https://github.com/xqyww123/isabelle-base-features/blob/main/fast_abbrev_printing/details.md)
explains the cause and the fix.
