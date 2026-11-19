import re, os
ids = [l.strip() for l in open('built_ids.txt') if l.strip()]
ROWS = '../../../lean/SignedDifferenceSets/TomographyQuotRows'
core = ["Tomography.not_hasSDS_quot", "Tomography.not_hasSDS_quot_nc", "Tomography.not_hasSDS_grp",
        "Tomography.not_hasSDS_grp_nc", "Tomography.fixed_lineQ", "Tomography.sum_contract_linesQ",
        "Tomography.exists_centeredQ", "Tomography.demands_lineQ", "Tomography.lists_of_orbSearch",
        "Tomography.lists_of_inSearch", "Tomography.lists_all_of_inSearch", "Tomography.closes_of_ptOK",
        "Tomography.closes_of_tomoGoL", "Tomography.inPart_of_top", "Tomography.tomoGoL_of_top",
        "Tomography.no_choiceL", "IsSDS.exists_translate_fixed_contract'"]
parts = [ids[i::3] for i in range(3)]
for pi, sel in enumerate(parts):
    out = ["import SignedDifferenceSets.TomographyQuotNC", "import SignedDifferenceSets.TomographySplit"]
    out += [f"import SignedDifferenceSets.TomographyQuotRows.{i}" for i in sel]
    out += ["", "open SignedDifferenceSets", ""]
    if pi == 0:
        out += [f"#print axioms {t}" for t in core]
    for i in sel:
        t = open(f'{ROWS}/{i}.lean', encoding='utf-8').read()
        m = re.search(r"theorem not_hasSDS : (¬ HasSDS \(.*?\) \d+ \(?-?\d+\)?) :=", t)
        out.append(f"#print axioms TomographyQuotRows.{i}.not_hasSDS")
        out.append(f"example : {m.group(1)} := TomographyQuotRows.{i}.not_hasSDS")
    open(f'AxC41_{pi}.lean', 'w', encoding='utf-8', newline='\n').write('\n'.join(out) + '\n')
    print(pi, len(sel))
