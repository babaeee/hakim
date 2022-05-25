if ! command -v wasm-pack &> /dev/null
then
    echo "installing rust..."
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
else
    echo "✓ rust exists"
fi
if ! command -v wasm-pack &> /dev/null
then
    echo "installing wasm-pack..."
    cargo install wasm-pack
    rustup target add wasm32-unknown-unknown
    exit
else
    echo "✓ wasm-pack exists"
fi

cd hakim-wasm
echo "building hakim wasm..."
wasm-pack build
