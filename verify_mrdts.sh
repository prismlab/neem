#!/bin/bash
fstar.exe --cache_checked_modules code/interface/App_mrdt.fsti
echo -e "\n"
fstar.exe --cache_checked_modules code/interface/Set_extended.fsti
echo -e "\n"
fstar.exe --cache_checked_modules code/interface/Set_extended.fst --include code/interface
echo -e "\n"
fstar.exe --cache_checked_modules code/interface/Map_extended.fsti --include code/interface
echo -e "\n"
fstar.exe --cache_checked_modules code/interface/Map_extended.fst --include code/interface
echo -e "\n"
fstar.exe --cache_checked_modules code/interface/Dependent_map.fsti --include code/interface
echo -e "\n"
fstar.exe --cache_checked_modules code/interface/Dependent_map.fst --include code/interface
echo -e "\n"

echo -e "\nVerifying MRDTs..\n"
results=()
files=(
  "Increment-only_counter"
  "PN_counter"
  "Enable-wins_flag"
  "Disable-wins_flag"
  "Grow-only_set"
   "Grow-only_map"
   "OR-set"
   "OR-set-efficient"
   "Remove-wins_set"
   "Set-wins_map"
   "Replicated-Growable-Array"
   "Optional_register"
   "Multi-valued_register"
)
for file in "${files[@]}"; do
  start_time=$(date +%s)
  if fstar.exe code/mrdts/$file/App_mrdt.fst \
      --include code/interface; then
    end_time=$(date +%s)
    time=$((end_time - start_time))
    results+=("$file $time")
    echo -e "Completed verification for $file \n"
  else
    echo "Error processing $file"
    exit 1
  fi
done

json_start_time=$(date +%s)
if fstar.exe --cache_checked_modules code/interface/Json.fsti --include code/interface && \
   fstar.exe code/mrdts/Json/Json.fst --include code/interface; then
  json_end_time=$(date +%s)
  json_time=$((json_end_time - json_start_time))
  echo "Completed verification for JSON-style MRDT"
  results+=("Json-style_MRDT $json_time")
else
  echo "Error processing JSON-style MRDT"
  exit 1
fi

echo -e "\nVerification Results:"
printf "%-30s %-20s\n" "MRDT" "Verification Time (s)"
printf "%-30s %-20s\n" "------------------------------" "--------------------"
for result in "${results[@]}"; do
  printf "%-30s %-20s\n" $(echo $result | awk '{print $1}') $(echo $result | awk '{print $2}')
done
