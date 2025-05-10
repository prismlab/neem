# Neem 

Neem is a framework for automated verification of mergeable replicated data types (MRDTs) and state-based convergent replicated data types (CRDTs). See https://dl.acm.org/doi/10.1145/3720452. 

## Development Environment

Easiest way to get started is to use the devcontainer.

```bash
$ git clone https://github.com/prismlab/neem
$ cd neem
$ code . # Start VSCode
```

VSCode will notify that there is a devcontainer associated with this repo and whether to open this repo in a devcontainer. 

<img width="478" alt="image" src="https://github.com/user-attachments/assets/b075dfea-bd34-416b-a6c9-ed6ab0917b22" />

Click "Reopen in Container".

<img width="624" alt="image" src="https://github.com/user-attachments/assets/12b9d66d-827c-4099-9a1f-de527fe3f2cf" />

Choose "from DockerHub" option. The repo will be opened in a devcontainer.

You can check whether everything works correctly by running 

```
$ ./verify_crdts.sh
```

to confirm that everything works fine. This will verify CRDT implementations and produce a table at the end summarising the verification time.

```
<snip>
Verification Results:
CRDT                           Verification Time (s)
------------------------------ --------------------
Increment-only_counter         2                   
PN_counter                     5                   
Grow-only_set                  2                   
Grow-only_map                  4                   
OR-Set                         4                   
2P-Set                         3                   
Multi-valued_register          2
```
