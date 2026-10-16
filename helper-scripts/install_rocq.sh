#!/bin/bash
# Installs Rocq 9.2.0 from the CI image, rocq/rocq-prover:9.2.0, without a Docker daemon.
#
# It downloads the image's layers from Docker Hub with curl, checks their digests, and unpacks
# the image's opam switch to /home/rocq/.opam/4.14.2+flambda, the path it has in the image and
# in CI. Rocq's binaries link only libc and libm, so they run on any x86-64 Linux with glibc.
#
# Run it as root, from anywhere:
#
#     helper-scripts/install_rocq.sh
#     export PATH=/home/rocq/.opam/4.14.2+flambda/bin:$PATH
#
# It needs bash, curl, tar and python3, about 1.1 GB of download and 2 GB of disk, and it does
# nothing when Rocq 9.2 is already installed there. An optional argument unpacks under another
# root instead of / (for testing, or without root); Rocq then needs /home/rocq to be a symlink to
# <root>/home/rocq, because its library paths are built in.
#
# Claude Code cloud sessions run it through .claude/hooks/session-start.sh.
set -euo pipefail

IMAGE=rocq/rocq-prover
TAG=9.2.0
SWITCH=home/rocq/.opam/4.14.2+flambda
DEST=${1:-/}
DEST=${DEST%/}      # "" for the root, so that $DEST/$SWITCH is an absolute path either way
ROOT=${DEST:-/}

if "$DEST/$SWITCH/bin/rocq" --version 2>/dev/null | grep -q "version 9.2"; then
  echo "Rocq 9.2 is already installed in $DEST/$SWITCH"
  exit 0
fi
for tool in curl tar python3; do
  command -v "$tool" >/dev/null || { echo "install_rocq.sh needs $tool" >&2; exit 1; }
done

WORK=$(mktemp -d "${TMPDIR:-/tmp}/rocq-image.XXXXXX")
trap 'rm -rf "$WORK"' EXIT

json() { python3 -I -c "import json, sys; print($1)"; }

echo "Fetching the manifest of $IMAGE:$TAG from Docker Hub"
TOKEN=$(curl -fsS "https://auth.docker.io/token?service=registry.docker.io&scope=repository:$IMAGE:pull" \
  | json 'json.load(sys.stdin)["token"]')
ACCEPT='application/vnd.docker.distribution.manifest.v2+json, application/vnd.oci.image.manifest.v1+json, application/vnd.docker.distribution.manifest.list.v2+json, application/vnd.oci.image.index.v1+json'
curl -fsS -H "Authorization: Bearer $TOKEN" -H "Accept: $ACCEPT" \
  "https://registry-1.docker.io/v2/$IMAGE/manifests/$TAG" > "$WORK/manifest.json"
# A multi-platform image answers with an index; pick linux/amd64 from it.
if [ "$(json 'int("manifests" in json.load(open("'"$WORK"'/manifest.json")))')" = 1 ]; then
  DIGEST=$(json '[m["digest"] for m in json.load(open("'"$WORK"'/manifest.json"))["manifests"] if m.get("platform", {}).get("os") == "linux" and m["platform"].get("architecture") == "amd64"][0]')
  curl -fsS -H "Authorization: Bearer $TOKEN" -H "Accept: $ACCEPT" \
    "https://registry-1.docker.io/v2/$IMAGE/manifests/$DIGEST" > "$WORK/manifest.json"
fi
LAYERS=$(json '"\n".join(l["digest"] for l in json.load(open("'"$WORK"'/manifest.json"))["layers"])')

i=0
for digest in $LAYERS; do
  i=$((i + 1))
  layer=$WORK/layer$i.tar.gz
  echo "Downloading layer $i ($digest)"
  curl -fsSL -H "Authorization: Bearer $TOKEN" -o "$layer" \
    "https://registry-1.docker.io/v2/$IMAGE/blobs/$digest"
  echo "${digest#sha256:}  $layer" | sha256sum -c --quiet
  tar -tzf "$layer" > "$layer.list"
  if ! grep -q "^$SWITCH/" "$layer.list"; then
    rm -f "$layer" "$layer.list"
    continue
  fi
  echo "Unpacking $SWITCH from layer $i"
  # Apply the layer's whiteouts first: ".wh..wh..opq" empties a directory, ".wh.<name>" removes <name>.
  { grep "^$SWITCH/.*/\.wh\." "$layer.list" || true; } | while read -r wh; do
    if [ "$(basename "$wh")" = ".wh..wh..opq" ]; then
      rm -rf "$DEST/$(dirname "$wh")"
    else
      rm -rf "$DEST/$(dirname "$wh")/$(basename "$wh" | sed 's/^\.wh\.//')"
    fi
  done
  mkdir -p "$ROOT"
  # .opam-switch holds opam's build leftovers and sources, which Rocq doesn't need.
  tar -xzf "$layer" -C "$ROOT" --no-same-owner \
    --exclude="$SWITCH/.opam-switch" --exclude='*/.wh.*' "$SWITCH"
  rm -f "$layer" "$layer.list"
done

echo
"$DEST/$SWITCH/bin/rocq" --version
echo
echo "Rocq is installed in $DEST/$SWITCH. Put it on the PATH with:"
echo "    export PATH=/home/rocq/.opam/4.14.2+flambda/bin:\$PATH"
if [ "$DEST" != "" ]; then
  echo "Then make /home/rocq a symlink to $DEST/home/rocq, since Rocq's library paths are built in."
fi
