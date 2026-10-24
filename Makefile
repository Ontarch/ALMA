.PHONY: everything index check html clean

AGDA       := agda
AGDAFLAGS  := -i src
EVERYTHING := src/Everything.agda
INDEX      := src/index.agda
OPTIONS    := --safe --cubical-compatible --guardedness --exact-split --double-check

SRCS := $(shell find src -name '*.agda' ! -name 'Everything.agda' ! -name 'index.agda' ! -name '.*')

MODULES := $(shell find src -name '*.agda' ! -name 'Everything.agda' ! -name 'index.agda' ! -name '.*' \
             | sed -e 's|^src/||' -e 's|/|.|g' -e 's|\.agda$$||' \
             | LC_COLLATE='C' sort)

everything: $(EVERYTHING)
index: $(INDEX)

$(EVERYTHING): $(SRCS)
	@if [ -z "$(MODULES)" ]; then echo "ERROR: no .agda files under src/" >&2; exit 1; fi
	@echo "{-# OPTIONS $(OPTIONS) #-}" > $@
	@echo "" >> $@
	@echo "module Everything where" >> $@
	@for file in $$(find src -name '*.agda' ! -name 'Everything.agda' ! -name 'index.agda' ! -name '.*' | LC_COLLATE='C' sort); do \
	  module=$$(echo "$$file" | sed -e 's|^src/||' -e 's|/|.|g' -e 's|\.agda$$||'); \
	  echo "" >> $@; \
	  awk 'BEGIN{ h=0 } /^----+$$/ { if (h) exit; h=1; next } h && /^-- / { print }' "$$file" >> $@; \
	  echo "import $$module" >> $@; \
	done
	@echo "Generated $@"

$(INDEX): $(SRCS)
	@if [ -z "$(MODULES)" ]; then echo "ERROR: no .agda files under src/" >&2; exit 1; fi
	@echo "{-# OPTIONS $(OPTIONS) #-}" > $@
	@echo "" >> $@
	@echo "module index where" >> $@
	@echo "" >> $@
	@echo "-- Module list with descriptions" >> $@
	@echo "import Everything" >> $@
	@echo "" >> $@
	@echo "-- All modules" >> $@
	@for m in $(MODULES); do echo "import $$m" >> $@; done
	@echo "Generated $@"

check: $(EVERYTHING)
	$(AGDA) $(AGDAFLAGS) $(EVERYTHING)

html: $(EVERYTHING) $(INDEX)
	$(AGDA) $(AGDAFLAGS) --html --html-dir=./docs $(INDEX)

clean:
	find src -name '*.agdai' -delete
	rm -f $(EVERYTHING) $(INDEX)
