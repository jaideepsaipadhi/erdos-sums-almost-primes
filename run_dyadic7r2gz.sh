#!/usr/bin/env bash
set -u

cat > patch_7r2gz.py << 'PYEOF'
#!/usr/bin/env python3
import sys, io, base64, gzip, hashlib

PATH = "Banksmartin/Basic.lean"
MD5 = "2e15e214f14841acbba9412a17d62a3e"

B = """
H4sIAEPpY2oC/+1ZT2/URhS/51O8GzZdlqy3h5ImkWgkVFQKFeKGUsvxzq4t22PH9oak6gGhCgHl
0FbqseLSSq3Ue+98lP0kfW/G3p0Zj0M2CX+EiFA2rN978/7N7/1mDEA/r/+Da9fg25u378JX92/e
3ft6C45hdwduDKCOShZM6COfzyL8ZDA5CSZxCAf5nE82oPkp5lXkh0FVL78J06Cq4jBIl99EwRGD
KM1nx36RV7AFzubW4qc/XNiG+yxIh/gE193aWf5PiDkHJ5DGPCjjOnK7tloxqzVnZdclwwcnSwOt
CY++rx/lfsp86UB0fEORYsdBWJ/do6OAx1U0RncWzx5Dgb+fgXMr5hWrh7fDEIrFk8ewePniePHy
58WTF+5wGqc1K8GZzjmK7+xCMfyujDPmDhQnAN26jo+3YQyLp79BEX9zq8wz4OCIBy6pwmYnxJjX
ZY7PIvyX1sqDEkvFKrgb1MO09vPSnzE05sEjDAkiPoIf8benKGCLyAD56AoGx3G5kVwO8ozNAs3Z
an5Q1UJU+zo/qIOYw+LV31GRsWyAbhUU6uLVP2SqyRI+8WVShhl5rpmQPhReytAJDxbP/8ToULex
NJSFtKmYPeIU8i8Zg6iyn+UT0cOiwiIsVNlE4cLVTM75NE8nbRW0R0FRpCdtKGFQTnx26P/AyhyD
KfslZcAky7KiPvHj6bSjIIuZQaSvWMWYppyjrYdKBrHX9iGoTWFpIwpz/Az6ipPdw9JkMfebwtjE
ZVYzkXVMUiablqSdg3h2j3JH0eScUSyQuaKY2T1baTI0UIhaZmI5WlrEKa1PjiZ+OU1ty4s2cDJZ
STIgt4m5DVYaI0Peoa1IOnI70rbtbYooG3pWox4ZtRtSfTJ0Qey+aZrj7sM4nEl85POcczbTAUb2
7jBlrmGglbAlhgAoE3DRn4usVJLRiBIYTAkK6XctM6wjxxIT1cSU1k0qyroDXi9OlI/gIcrJRjVW
aVIbko+Oh07+7kpPVwZ5XmY+n2ddm15otWnJGOKaRPgGub0GLbmnaUtvJmVeCGT/tUX280F7+8hI
qyIoGqdpqXFjb4CYZcF92WmaqR3VxUsYPnDayp0O04Ctmmc+jQNWLz1psK751gff7ZlYBe9M60Ls
+Nf/WjNEnlAkEQrt7OrdVPDl+tqAKeU4GpASwp3bWXFWU5z6OtstxnR6+sIjbu0Bd+njTRo8LghC
KOjWkh1MpPRYQcCxjoCfIU8QSKs6dDqeEC5W8zBUcGhmBYfGwzHF2786rtjwHAm2wWRCcwn8Dm4Q
BKMYDizaKCKp+5oQbxEEMWaMxfXUxwJ5Wv4nOxizqEp0AItUFk9/kciyb6ANtkdmEMlLhJs3gc3G
Wbc/Khvl3IOrCvNWObgL34PD4RqMXLjamYeO0xq/rlB4+ZVLNuOpqKSkGgUdRjjWl6UVI+4r3HFP
4cAPutvG2JTYbau92dFZbW5/IKDo9F394GPEBYz6PhksdM7VDw0jQ7pno9oZV2Hl8l4/2mj+6PzK
emjrYQUN9DMTAxfP/xKmNX1CjRnz6aTMGvZUR3E5Qc1Wz0LoZCq7+R2J9I6UhPUCZ5MNQeO8HoVu
Sj0jp73hC+QUKOSLs35LjchFyo0BffHUl2GJhhxANk8JZvc7Z+loZAAdcgRP2QVEGTCH+NFgoCE+
DcL3SMI+JKwzSN/5fHlbiVw7lW9rAFBztgCLPYl9ZU7aB8hFxTnjnY1XWLx42vb77TwkjtShsh/h
FJMAoF5T5OGKhMtJRlcGab10zShVc0KWrCgRbXtKGvUWI/Hn7xYu6LZO09iUEC2aOun2eWLp88Ta
5z0dkkCUaMy253oob07ISaebkg5lSNagDEmXMiQNZUjWogzJOSlDYlzSvA/K4Iz1UFcZPDNxSKzE
QdRGJLSzMrZQ0nMJrrjgnvF6vT3FE2DKLWe7M+m/siJvhhrRQKWqSGM6XVWw/eVu9zC0JANjKxmg
DMk7A/qrWVZCd2S42NzWnJAd0iyDOs7pdt+X7y6u4GbCHKPdkk1TGorqnb/UvnPHX2JNm1SqZ++7
BeVlhBq5tLbXY+1sI1vrm1VJ0OyQ2rTIHy2/Wbntm68mUIxWfzNBsMdokI1+O9w6gemYS47SwV7l
hGHOZyWM1Cmj3ak0nA9bK/XZIQZwPpbjjL/4HBWP+6JTkbgTq9Tda/RPi/y68SbLmgaqhHZxEHOz
d0OiuOdc1jyQO3t0DUJ19TY3Ny8ahPTv0OjjNU12YLBFEaW5dUTpaXLuuqs3ikPLAbganTuRRgft
tD20J0b0OpbaWaUVeumhmE0XqVHXUd3cZfkrLriq0YB83reOCkRUcexr8dkv41lEd7zR4cYp0zMM
0vDDv1UXyp9OnXLY0ZldMe9/On6q2ZkGoZacs496W3rWPOYooVzohOF231la93jKpnXD21Y855LC
X29sr+Uw0sMedy8y8JdMpZOAC49hJAUb/wMSGkQlsCMAAA==
"""

s = gzip.decompress(base64.b64decode("".join(B.split()))).decode("utf-8")
if hashlib.md5(s.encode()).hexdigest() != MD5:
    print("ERROR: payload md5 mismatch - aborting."); sys.exit(1)
with io.open(PATH, "r", encoding="utf-8") as fh:
    f = fh.read()
stub = "      \u00b7 sorry -- MAINBRANCH-TODO\n"
if f.count(stub) != 1:
    print("ERROR: stub locator - found", f.count(stub), "matches"); sys.exit(1)
f = f.replace(stub, s.rstrip("\n") + "\n")
with io.open(PATH, "w", encoding="utf-8") as fh:
    fh.write(f)
print("OK: main branch installed.")
PYEOF

if python3 patch_7r2gz.py; then
  echo "===== lake build ====="
  lake build
else
  echo "PATCH FAILED - skipping build. Paste this whole output."
fi
