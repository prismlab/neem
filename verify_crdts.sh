#!/bin/bash
fstar.exe --cache_checked_modules code/interface/App_crdt.fsti
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

echo -e "\nVerifying CRDTs..\n"
results=()
files=(
  "Increment-only_counter"
  "PN_counter"
  "Grow-only_set"
   "Grow-only_map"
   "OR-Set"
   "2P-Set"
   "Multi-valued_register"
)
for file in "${files[@]}"; do
  start_time=$(date +%s)
  if fstar.exe code/crdts/$file/App_crdt.fst \
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

echo -e "\nVerification Results:"
printf "%-30s %-20s\n" "CRDT" "Verification Time (s)"
printf "%-30s %-20s\n" "------------------------------" "--------------------"
for result in "${results[@]}"; do
  printf "%-30s %-20s\n" $(echo $result | awk '{print $1}') $(echo $result | awk '{print $2}')
done
