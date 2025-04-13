#!/usr/bin/env bash

check_command() {
  if ! command -v $1 &> /dev/null; then
    echo "[-] $1 not found. Please install it."
    exit 1
  fi
}

spinner() {
  local pid=$1
  local msg=$2
  local delay=0.2
  local spin='-\|/'

  while kill -0 "$pid" 2>/dev/null; do
    for i in {0..3}; do
      printf "\r[%c] %s" "${spin:$i:1}" "$msg"
      sleep $delay
    done
  done
  printf "\r"
}

upgrade_pip() {
  local LOG_FILE="upgrade_pip.log"

  pip install --upgrade pip > "$LOG_FILE" 2>&1 &
  local upgrade_pip=$!
  spinner "$upgrade_pip" "Upgrading pip..."

  wait "$upgrade_pip"
  local exit_code=$?
  
  if [ "$exit_code" -ne 0 ]; then
    echo "[-] Upgrading pip failed (exit code $exit_code). See below for the output."
    cat "$LOG_FILE"
    exit "$exit_code"
  fi

  echo "[+] Pip upgraded successfully"
  rm -f "$LOG_FILE"
}

install_deps() {
  local LOG_FILE="pip_install.log"
  # 1) Run pip in the background, capture its PID
  #    (sending all pip output to /dev/null)
  pip install -r requirements.txt > "$LOG_FILE" 2>&1 &
  local pip_pid=$!

  # 2) Call spinner on that PID
  spinner "$pip_pid" "Installing dependencies..."

  # 3) Wait for pip to finish, capture exit code
  wait "$pip_pid"
  local exit_code=$?

  # 4) If pip failed, handle it
  if [ "$exit_code" -ne 0 ]; then
    echo "[-] Installation failed. See below for pip output."
    cat "$LOG_FILE"
    exit "$exit_code"
  fi

  echo "[+] Dependencies installed successfully!"
  rm -f "$LOG_FILE"
}

# Check whether python3 exists, otherwise fall back to python
if command -v python3 &>/dev/null; then
    PYTHON_CMD="python3"
elif command -v python &>/dev/null; then
    PYTHON_CMD="python"
else
    echo "[-] No Python interpreter found! Aborting."
    exit 1
fi

REQUIRED_VERSION="3"
INSTALLED_VERSION=$($PYTHON_CMD -c 'import sys; print(f"{sys.version_info.major}")')

# Compare installed python vs. required:
if (( $(echo "$INSTALLED_VERSION < $REQUIRED_VERSION" | bc -l) )); then
    echo "[-] Python $REQUIRED_VERSION is required. You have $INSTALLED_VERSION. Aborting."
    exit 1
fi

check_command pip

# 1) Check if script is inside a venv
if [ -z "$VIRTUAL_ENV" ]; then
  echo "[*] Checking status of virtual environment..."
  if [ -d "venv" ]; then
    echo "[*] 'venv' folder already exists. Skipping creation."
  else
    echo "[+] Creating virtual environment in 'venv'..."
    $PYTHON_CMD -m venv venv
  fi
    source venv/bin/activate
else 
  echo "[+] Detected virtual environment: $VIRTUAL_ENV"
fi

# 2) Upgrade pip
upgrade_pip
# 3) Install dependencies
install_deps

echo "[+] Setup complete. You can activate virtual environment with 'source venv/bin/{activate_script}."
echo "    To deactivate, run: deactivate"
