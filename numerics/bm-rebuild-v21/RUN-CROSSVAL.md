# One-file setup for the crossval run

    cd /workspace
    tar xzf bm-rebuild-v21.tar.gz
    cd bm-rebuild-v21          # note: directory name matches this tarball
    python3 crossval_certificate.py /workspace/certificate-k200.json

delta_table.jsonl in this package already covers m=0..1000 — no copy/rename needed.
First run will likely stop in load_fk() printing your certificate's top-level
keys; edit load_fk() (top of crossval_certificate.py) to map your schema to
{k: (lo_string, hi_string)} and rerun. Paste the schema keys to Claude if unsure.
