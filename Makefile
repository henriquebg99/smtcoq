all:
	cd src && $(MAKE)

install: all
	cd src && $(MAKE) install

clean: 
	cd src && $(MAKE) clean