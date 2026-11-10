import re, sys, ast
def lean_def(path, name):
    src = open(path, encoding='utf-8').read()
    m = re.search(r'^def ' + name + r' : [^\n]*:=\s*\n(.*?)(?=\n\n|\n/--|\ntheorem|\n--)', src, re.S | re.M)
    return ast.literal_eval(m.group(1).strip()) if m else None
if __name__ == '__main__':
    for path in sys.argv[1:]:
        for nm in ('v0', 'w', 'fr', 'ex'):
            v = lean_def(path, nm)
            if v is not None: print(path.split('/')[-1], nm, len(v), sorted(map(tuple, v)) if nm in ('v0','w') else v)
