#pragma once

namespace
{
	const auto Free = [](auto p) { delete(p); };
	template<typename T>

	using SafePtr = std::unique_ptr<T, decltype(Free)>;

	template<typename T>
	SafePtr<T> getSafePtr()
	{
		return SafePtr<T>{new T, Free};
	}

}


