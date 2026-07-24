import io
s = io.open('patch_7r1b.py', encoding='utf-8').read()
old = '"          linarith\\n'
new = '"        linarith\\n'
n = s.count(old)
if n != 2:
    print("ERROR: expected 2 occurrences of the 10-space locator, found", n)
    raise SystemExit(1)
io.open('patch_7r1b.py', 'w', encoding='utf-8').write(s.replace(old, new))
print("OK: locator corrected to 8 spaces (both occurrences)")
