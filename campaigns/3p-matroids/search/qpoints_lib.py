import json, subprocess
from pathlib import Path
GP = Path(__file__).resolve().parents[3].as_posix() + "/"  # the repo root
def enc_of(name):
    return json.loads(subprocess.run(["python", GP+"tools/encode-matroid.py", GP+f"campaigns/3p-matroids/matroids/{name}.json"], capture_output=True, text=True).stdout)
