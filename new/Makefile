FILES = Append-only_log Increment-only_counter PN_counter \
	Last-writer-wins_register Enable-wins_flag \
	Grow-only_set Grow-only_map

all: app.fsti framework app.fst clean

app.fsti: SeqUtils.fst
	fstar.exe App.fsti

framework: App.fsti SeqUtils.fst
	fstar.exe Framework.fst

app.fst: App.fsti Framework.fst SeqUtils.fst
	for file in $(FILES); do \
		fstar.exe $$file/App.fst; \
	done

clean:
	rm -f *~
