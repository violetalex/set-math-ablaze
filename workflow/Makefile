.PHONY: help test selfcheck check doctor clean

help:
	@echo "make test       跑单元测试"
	@echo "make selfcheck  验证门禁本身按预期工作"
	@echo "make check      在当前工程跑验收（需在当前工程目录）"
	@echo "make doctor     环境体检"

test:
	python3 -I run_tests.py -v

selfcheck:
	./bin/mathlean selfcheck

check:
	./bin/mathlean check

doctor:
	./bin/mathlean doctor

clean:
	find . -name __pycache__ -type d -exec rm -rf {} + 2>/dev/null || true
	rm -rf build dist *.egg-info
