export UV_SKIP_WHEEL_FILENAME_CHECK=1
export UV_LINK_MODE=copy

git clone --recursive https://github.com/FurkanGozukara/Trellis_2_3D_Generator

cd Trellis_2_3D_Generator

git reset --hard

git pull

python3 -m venv venv

source ./venv/bin/activate

python -m pip install --upgrade pip

pip install uv

cd ..

uv pip install -r requirements_trellis.txt

uv pip install --no-deps https://huggingface.co/MonsterMMORPG/Wan_GGUF/resolve/main/flex_gemm-0.0.1-cp310-cp310-linux_x86_64.whl
uv pip install --no-deps https://huggingface.co/MonsterMMORPG/Wan_GGUF/resolve/main/o_voxel-0.0.2-cp310-cp310-linux_x86_64.whl
uv pip install --no-deps git+https://github.com/Luo-Yihao/FaithC.git

set HF_HUB_ENABLE_HF_TRANSFER=1

python3 HF_model_downloader.py