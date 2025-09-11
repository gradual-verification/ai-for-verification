#!/usr/bin/env python3
"""
Verification Counter - Standalone Script
Analyzes verification constructs in VeriFast C files and generates Excel report.

This is a standalone version of the Jupyter notebook that you can run directly.
"""

import re
import os
import glob
import pandas as pd
from collections import defaultdict
from itertools import groupby

def main():
    print("🔬 Verification Counter - Starting Analysis")
    print("=" * 60)
    
    # ─── CONFIGURE THIS ─────────────────────────────────────────────────────────────
    # change path to your path
    folder_path = '../input-output-pairs/correct/'
    file_patterns = ["*.c"]  # Focus on .c files for verification analysis
    # ────────────────────────────────────────────────────────────────────────────────
    
    # Allow optional //@ prefix on single-line declarations; keep plain form for block lines
    categories = {
        'Predicate Declaration': re.compile(r'^\s*(?://@\s*)?predicate\b'),
        'Fixpoint Declaration':   re.compile(r'^\s*(?://@\s*)?fixpoint(_auto)?\b'),
        'Lemma Declaration':      re.compile(r'^\s*(?://@\s*)?lemma(_auto)?\b'),
        'Inductive Declaration':  re.compile(r'^\s*(?://@\s*)?inductive\b'),
        'Precondition':           re.compile(r'^\s*//@\s*requires\b'),
        'Postcondition':          re.compile(r'^\s*//@\s*ensures\b'),
        'Close':                  re.compile(r'^\s*//@\s*close\b'),
        'Open':                   re.compile(r'^\s*//@\s*open\b'),
    }
    
    bool_expr_patterns = [
        r'\btrue\b',
        r'\bfalse\b',
        r'\b\w+\s*\?\s*\w+\s*:\s*\w+\b',
        r'(?<![*/<>=!])==|!=|>=|<=|<|>(?![=])',
        r'\b\w+\s*[+\-*/%]=\s*\w+\b',
        r'\b\w+\s*[+\-*/%]\s*\w+\b',
        r'\b\w+\s*=\s*\w+\b',
    ]
    
    ignore_patterns = [
        r'&\*&',
        r'\bint\s*\*\s*\w+',
        r'\w+\s*\*\s*\w+',
        r'//\s*@'
    ]
    
    fractional_permission_patterns = [
        r'\[\?*[a-zA-Z_]\]',
        r'\[\d+/\d+\]',
        r'\[(\d*\.\d+|\.\d+|\d+)\]'
    ]
    
    sep_arrow_pattern      = re.compile(r'\|->')
    empty_heap_pattern     = re.compile(r'\bemp\b')
    malloc_call_pattern    = re.compile(r'\bmalloc\s*\(')
    malloc_block_pattern   = re.compile(r'\bmalloc_block_\w+\b')
    malloc_generic_pattern = re.compile(r'\bmalloc_\w+\b')
    
    def clean_text(text):
        for pat in ignore_patterns:
            text = re.sub(pat, '', text)
        return text
    
    def count_boolean_expressions(text_block):
        cleaned = clean_text(text_block)
        return sum(len(re.findall(p, cleaned)) for p in bool_expr_patterns)
    
    def count_fractional_permissions(text_block):
        return sum(len(re.findall(p, text_block)) for p in fractional_permission_patterns)
    
    def count_sep_arrows(text_block):
        return len(sep_arrow_pattern.findall(text_block))
    
    def count_empty_heap(text_block):
        return len(empty_heap_pattern.findall(text_block))
    
    def count_malloc_patterns(text_block):
        call   = len(malloc_call_pattern.findall(text_block))
        block  = len(malloc_block_pattern.findall(text_block))
        tmp    = malloc_block_pattern.sub('', text_block)
        generic= len(malloc_generic_pattern.findall(tmp))
        return call + block + generic
    
    def count_asserts(text_block):
        return sum(1 for l in text_block.splitlines()
                   if l.strip().startswith("assert") or l.strip().startswith("//@ assert"))
    
    # Helper: strip a leading //@ for declaration name extraction on single-line comments
    def _strip_at_prefix(s: str) -> str:
        return re.sub(r'^\s*//@\s*', '', s)
    
    def extract_predicate_name(line):
        line = _strip_at_prefix(line)
        m = re.match(r'^\s*predicate\s+([A-Za-z_]\w*)\s*\(', line)
        return m.group(1) if m else None
    
    def extract_fixpoint_name(line):
        line = _strip_at_prefix(line)
        m = re.match(r'^\s*fixpoint(?:_auto)?\s+\w+\s+([A-Za-z_]\w*)\s*\(', line)
        return m.group(1) if m else None
    
    def extract_lemma_name(line):
        line = _strip_at_prefix(line)
        # BUGFIX: make _auto optional
        m = re.match(r'^\s*lemma(?:_auto)?\s+\w+\s+([A-Za-z_]\w*)\s*\(', line)
        return m.group(1) if m else None
    
    def extract_inductive_name(line):
        line = _strip_at_prefix(line)
        m = re.match(r'^\s*inductive\s+([A-Za-z_]\w*)\b', line)
        return m.group(1) if m else None
    
    def count_name_usages(text_block, category, decl_sets, usage_counts):
        # Avoid counting the declaration's own first line by skipping it if it looks like a decl
        lines = text_block.splitlines()
        if lines and any(pat.match(lines[0]) for pat in (categories['Predicate Declaration'],
                                                         categories['Fixpoint Declaration'],
                                                         categories['Lemma Declaration'],
                                                         categories['Inductive Declaration'])):
            search_text = "\n".join(lines[1:])
        else:
            search_text = text_block
    
        for kind, names in decl_sets.items():
            for name in names:
                pattern = r'\b' + re.escape(name) + (r'\s*\(' if kind != 'Inductive' else r'\b')
                usage_counts[category][kind] += len(re.findall(pattern, search_text))
    
    # Collect all summary rows for Excel
    summary_rows = []
    
    # Collect all file paths (recursively scan subdirectories)
    paths = []
    for pat in file_patterns:
        paths.extend(glob.glob(os.path.join(folder_path, "**", pat), recursive=True))
    paths = sorted(paths)
    
    print(f"Found {len(paths)} files to analyze...")
    
    processed_files = 0
    for filepath in paths:
        grouped_blocks      = defaultdict(list)
        expression_counts   = defaultdict(int)
        permission_counts   = defaultdict(int)
        sep_arrow_counts    = defaultdict(int)
        empty_heap_counts   = defaultdict(int)
        malloc_total_counts = defaultdict(int)
        assert_counts       = defaultdict(int)
        usage_counts        = defaultdict(lambda: defaultdict(int))
        declared_predicates = set()
        declared_fixpoints  = set()
        declared_lemmas     = set()
        declared_inductives = set()
    
        try:
            with open(filepath, 'r', errors='ignore') as f:
                lines = f.readlines()
        except Exception as e:
            print(f"Error reading {filepath}: {e}")
            continue
    
        i = 0
        while i < len(lines):
            line = lines[i].rstrip('\n')
    
            if line.strip().startswith("/*@"):
                block_lines = []
                i += 1
                # capture lines up to and including @*/
                while i < len(lines):
                    block_lines.append(lines[i].rstrip('\n'))
                    if "@*/" in lines[i]:
                        break
                    i += 1
    
                current_subblock = []
                current_category = None
    
                def flush_subblock():
                    if not current_subblock:
                        return
                    full = "\n".join(current_subblock)
                    cat = current_category or 'Other'
                    grouped_blocks[cat].append(full)
    
                    expression_counts[cat]   += count_boolean_expressions(full)
                    permission_counts[cat]   += count_fractional_permissions(full)
                    sep_arrow_counts[cat]    += count_sep_arrows(full)
                    empty_heap_counts[cat]   += count_empty_heap(full)
                    malloc_total_counts[cat] += count_malloc_patterns(full)
                    assert_counts[cat]       += count_asserts(full)
                    decl_sets = {
                        'Predicate': declared_predicates,
                        'Fixpoint': declared_fixpoints,
                        'Lemma': declared_lemmas,
                        'Inductive': declared_inductives
                    }
                    count_name_usages(full, cat, decl_sets, usage_counts)
    
                    # Register declarations AFTER counting to avoid self-counting
                    for l in current_subblock:
                        if categories['Predicate Declaration'].match(l):
                            n = extract_predicate_name(l)
                            if n: declared_predicates.add(n)
                        elif categories['Fixpoint Declaration'].match(l):
                            n = extract_fixpoint_name(l)
                            if n: declared_fixpoints.add(n)
                        elif categories['Lemma Declaration'].match(l):
                            n = extract_lemma_name(l)
                            if n: declared_lemmas.add(n)
                        elif categories['Inductive Declaration'].match(l):
                            n = extract_inductive_name(l)
                            if n: declared_inductives.add(n)
    
                for bl in block_lines:
                    matched = False
                    for cat, pat in categories.items():
                        if pat.search(bl):
                            flush_subblock()
                            current_subblock = [bl]
                            current_category = cat
                            matched = True
                            break
                    if not matched:
                        current_subblock.append(bl)
    
                flush_subblock()
    
            elif line.strip().startswith("//@"):
                cat = 'Other'
                for c, pat in categories.items():
                    if pat.search(line):
                        cat = c
                        break
                grouped_blocks[cat].append(line)
    
                expression_counts[cat]   += count_boolean_expressions(line)
                permission_counts[cat]   += count_fractional_permissions(line)
                sep_arrow_counts[cat]    += count_sep_arrows(line)
                empty_heap_counts[cat]   += count_empty_heap(line)
                malloc_total_counts[cat] += count_malloc_patterns(line)
                assert_counts[cat]       += count_asserts(line)
    
                decl_sets = {
                    'Predicate': declared_predicates,
                    'Fixpoint': declared_fixpoints,
                    'Lemma': declared_lemmas,
                    'Inductive': declared_inductives
                }
                count_name_usages(line, cat, decl_sets, usage_counts)
    
                # Register single-line declarations (allowing //@ prefix)
                if categories['Predicate Declaration'].match(line):
                    n = extract_predicate_name(line)
                    if n: declared_predicates.add(n)
                elif categories['Fixpoint Declaration'].match(line):
                    n = extract_fixpoint_name(line)
                    if n: declared_fixpoints.add(n)
                elif categories['Lemma Declaration'].match(line):
                    n = extract_lemma_name(line)
                    if n: declared_lemmas.add(n)
                elif categories['Inductive Declaration'].match(line):
                    n = extract_inductive_name(line)
                    if n: declared_inductives.add(n)
    
            i += 1
    
        # Summarize per file
        for cat in sorted(grouped_blocks):
            blk = len(grouped_blocks[cat])
            # Use relative path from the correct/ folder for better identification
            relative_path = os.path.relpath(filepath, folder_path)
            summary_rows.append({
                "File": relative_path,  # Show relative path instead of just filename
                "Category": cat,
                "#Blk": blk,
                "BoolExpr": expression_counts[cat],
                "Perms": permission_counts[cat],
                "|->": sep_arrow_counts[cat],
                "Emp": empty_heap_counts[cat],
                "Malloc": malloc_total_counts[cat],
                "Asserts": assert_counts[cat],
                "Pred": usage_counts[cat]['Predicate'],
                "Fix": usage_counts[cat]['Fixpoint'],
                "Lemma": usage_counts[cat]['Lemma'],
                "Ind": usage_counts[cat]['Inductive']
            })
        
        processed_files += 1
        if processed_files % 10 == 0:
            print(f"Processed {processed_files}/{len(paths)} files...")
    
    # ────────────────────────────────────────────────────────────────────────────────
    # 📝 Write to Excel with filename headers and spacing
    # ────────────────────────────────────────────────────────────────────────────────
    print(f"\nProcessed all {processed_files} files. Generating Excel report...")
    
    summary_rows.sort(key=lambda x: x["File"])
    output_rows = []
    
    for file_name, rows in groupby(summary_rows, key=lambda x: x["File"]):
        output_rows.append({"File": file_name})  # File header
        output_rows.extend(list(rows))           # File rows
        output_rows.append({})                   # Spacer
    
    df = pd.DataFrame(output_rows)
    output_excel_path = os.path.join(folder_path, "..", "verification_analysis_summary.xlsx")
    
    try:
        df.to_excel(output_excel_path, index=False)
        print(f"\n✅ Summary Excel file written to: {output_excel_path}")
        print(f"📊 Total rows in Excel: {len(output_rows)}")
        print(f"📁 Found {len(summary_rows)} verification constructs across {processed_files} files")
        
        # Print some summary statistics
        if summary_rows:
            total_predicates = sum(row.get('#Blk', 0) for row in summary_rows if row.get('Category') == 'Predicate Declaration')
            total_requires = sum(row.get('#Blk', 0) for row in summary_rows if row.get('Category') == 'Precondition')
            total_ensures = sum(row.get('#Blk', 0) for row in summary_rows if row.get('Category') == 'Postcondition')
            total_arrows = sum(row.get('|->', 0) for row in summary_rows)
            
            print(f"\n📈 Summary Statistics:")
            print(f"   Predicate Declarations: {total_predicates}")
            print(f"   Preconditions (requires): {total_requires}")
            print(f"   Postconditions (ensures): {total_ensures}")
            print(f"   Separation Logic Arrows (|->): {total_arrows}")
        
        print(f"\n🎉 Analysis complete! Open the Excel file to view detailed results.")
        
    except Exception as e:
        print(f"❌ Error writing Excel file: {e}")
        print("💡 You can still view the results by modifying the script to print them instead.")

if __name__ == "__main__":
    main()
