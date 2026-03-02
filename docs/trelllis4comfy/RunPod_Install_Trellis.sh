export UV_SKIP_WHEEL_FILENAME_CHECK=1
export UV_LINK_MODE=copy

git clone --recursive https://github.com/FurkanGozukara/Trellis_2_3D_Generator

cd Trellis_2_3D_Generator

git reset --hard

git pull

# Check if Python 3.10 is installed
if ! command -v python3.10 &> /dev/null; then
    echo "Python 3.10 not found. Installing Python 3.10..."
    apt-get update
    apt-get install -y python3.10 python3.10-venv python3.10-dev
else
    echo "Python 3.10 found."
fi

# Check if python3.10-venv is available
if ! python3.10 -m venv --help &> /dev/null; then
    echo "python3.10-venv not found. Installing..."
    apt-get update
    apt-get install -y python3.10-venv
fi

# Create virtual environment with Python 3.10
echo "Creating virtual environment with Python 3.10..."
python3.10 -m venv venv

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