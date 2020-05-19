FILE=Invertibility.agda

all: 
	@echo "This command will take time (around a few tens of minutes)."
	@echo "Since most of the time is spect for termination checking,"
	@echo "consider uncommenting {-# TERMINATING #-} (two places)"
	@echo "in 'Definitional.agda', if you trust us."
	@echo 
	agda $(FILE)


